// Lean compiler output
// Module: Lean.DocString.Extension
// Imports: public import Lean.DeclarationRange public import Lean.DocString.Types public import Init.Data.String.Extra public import Init.Data.String.TakeDrop public import Init.Data.String.Search public import Init.Data.String.Length import Init.Omega
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_instReprDeclarationRange_repr___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Doc_instReprMathMode_repr(uint8_t, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Std_Format_nestD(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRange_default;
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "{ val :="};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__2_value;
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Dynamic.mk "};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__3 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__3_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__4 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__2_value),((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__4_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__5 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__5_value;
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " _ }"};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__6 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__6_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__7 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprElabInline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprElabInline___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprElabInline___closed__0 = (const lean_object*)&l_Lean_instReprElabInline___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprElabInline = (const lean_object*)&l_Lean_instReprElabInline___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprElabBlock = (const lean_object*)&l_Lean_instReprElabInline___closed__0_value;
static const lean_array_object l_Lean_instInhabitedVersoDocString_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedVersoDocString_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedVersoDocString_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedVersoDocString_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedVersoDocString_default = (const lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedVersoDocString = (const lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "doc"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "verso"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(146, 8, 133, 236, 68, 139, 240, 234)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(153, 72, 77, 160, 222, 42, 129, 126)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "whether to use Verso syntax in docstrings"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(3, 233, 138, 33, 66, 196, 218, 104)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 198, 182, 78, 108, 58, 220, 60)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_doc_verso;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(146, 8, 133, 236, 68, 139, 240, 234)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(153, 72, 77, 160, 222, 42, 129, 126)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(237, 134, 110, 210, 89, 29, 102, 103)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "whether to use Verso syntax in module docstrings (falls back to `doc.verso` if not set)"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(3, 233, 138, 33, 66, 196, 218, 104)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 198, 182, 78, 108, 58, 220, 60)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(228, 159, 139, 71, 221, 243, 206, 45)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_doc_verso_module;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "docStringExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(220, 176, 252, 112, 223, 70, 141, 135)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_docStringExt;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DocString"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 151, 103, 225, 164, 122, 118, 127)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Extension"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 24, 255, 250, 40, 109, 111, 101)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(90, 73, 37, 46, 133, 14, 26, 13)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 17, 71, 28, 211, 27, 155, 40)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inheritDocStringExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 170, 221, 64, 52, 198, 31, 56)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "versoDocStringExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 29, 13, 95, 132, 33, 43, 178)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringExt;
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings();
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addDocStringCore___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration `"};
static const lean_object* l_Lean_addDocStringCore___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_addDocStringCore___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_addDocStringCore___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDocStringCore___redArg___lam__2___closed__1;
static const lean_string_object l_Lean_addDocStringCore___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is in an imported module"};
static const lean_object* l_Lean_addDocStringCore___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_addDocStringCore___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_addDocStringCore___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDocStringCore___redArg___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_removeDocStringCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_removeDocStringCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_removeDocStringCore___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_removeDocStringCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "invalid doc string removal, declaration `"};
static const lean_object* l_Lean_removeDocStringCore___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_removeDocStringCore___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_removeDocStringCore___redArg___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addInheritedDocString___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "invalid `[inherit_doc]` attribute, cycle detected"};
static const lean_object* l_Lean_addInheritedDocString___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_addInheritedDocString___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addInheritedDocString___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addInheritedDocString___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "invalid `[inherit_doc]` attribute, declaration `"};
static const lean_object* l_Lean_addInheritedDocString___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addInheritedDocString___redArg___lam__3___closed__1;
static const lean_string_object l_Lean_addInheritedDocString___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` already has an `[inherit_doc]` attribute"};
static const lean_object* l_Lean_addInheritedDocString___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___lam__3___closed__2_value;
static lean_once_cell_t l_Lean_addInheritedDocString___redArg___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addInheritedDocString___redArg___lam__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_addInheritedDocString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addInheritedDocString___redArg___closed__0 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_findInternalDocString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_findInternalDocString_x3f___closed__0 = (const lean_object*)&l_Lean_findInternalDocString_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentArray_push___redArg, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moduleDocExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 198, 210, 20, 250, 243, 120, 74)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_getMainModuleDoc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getMainModuleDoc___closed__0;
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object*);
static lean_once_cell_t l_Lean_getModuleDoc_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getModuleDoc_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_getDocStringText___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___redArg___closed__0 = (const lean_object*)&l_Lean_getDocStringText___redArg___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___redArg___closed__1;
static const lean_string_object l_Lean_getDocStringText___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_getDocStringText___redArg___closed__2 = (const lean_object*)&l_Lean_getDocStringText___redArg___closed__2_value;
static const lean_string_object l_Lean_getDocStringText___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_getDocStringText___redArg___closed__3 = (const lean_object*)&l_Lean_getDocStringText___redArg___closed__3_value;
static const lean_string_object l_Lean_getDocStringText___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_getDocStringText___redArg___closed__4 = (const lean_object*)&l_Lean_getDocStringText___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_isVersoDocComment___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_isVersoDocComment___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isVersoDocComment___closed__0_value_aux_0),((lean_object*)&l_Lean_getDocStringText___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_isVersoDocComment___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isVersoDocComment___closed__0_value_aux_1),((lean_object*)&l_Lean_getDocStringText___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_isVersoDocComment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isVersoDocComment___closed__0_value_aux_2),((lean_object*)&l_Lean_getDocStringText___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 150, 193, 173, 39, 149, 4, 235)}};
static const lean_object* l_Lean_isVersoDocComment___closed__0 = (const lean_object*)&l_Lean_isVersoDocComment___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_isVersoDocComment(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isVersoDocComment___boxed(lean_object*);
static const lean_array_object l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value;
static lean_once_cell_t l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instInhabitedSnippet;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object*);
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.text"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__1 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3;
static lean_once_cell_t l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.emph"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__5 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__5_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__6 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__6_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7_value;
static const lean_string_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7_value;
static const lean_string_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object*);
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.bold"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__8 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__8_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__8_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__9 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__9_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.code"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__11 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__11_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__11_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__12 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__12_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.math"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__14 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__14_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__14_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__15 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__15_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Doc.Inline.linebreak"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__17 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__17_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__17_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__18 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__18_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.link"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__20 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__20_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__20_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__21 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__21_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__21_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Doc.Inline.footnote"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__23 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__23_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__23_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__24 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__24_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__24_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Doc.Inline.image"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__26 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__26_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__26_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__27 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__27_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__27_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Doc.Inline.concat"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__29 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__29_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__29_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__30 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__30_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__30_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Doc.Inline.other"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__32 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__32_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__32_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__33 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__33_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__33_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object*);
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Doc.Block.para"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Doc.Block.code"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__3 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__3_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__3_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__4 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__4_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Doc.Block.ul"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__6 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__6_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__6_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__7 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8_value;
static const lean_string_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__4 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__4_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value;
static const lean_string_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "contents"};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__2_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_value),((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object*);
static const lean_string_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9;
static lean_once_cell_t l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11_value;
static const lean_string_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__8_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object*);
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Doc.Block.ol"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__9 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__9_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__9_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__10 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__10_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Doc.Block.dl"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__13 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__13_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__13_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__14 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__14_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15_value;
static const lean_string_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__1_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__2_value),((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4;
static const lean_string_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "desc"};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object*);
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Doc.Block.blockquote"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__16 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__16_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__16_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__17 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__17_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Doc.Block.concat"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__19 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__19_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__19_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__20 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__20_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__20_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Block.other"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__22 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__22_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__22_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__23 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__23_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__23_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object*);
static const lean_string_object l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "title"};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__1_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__2_value),((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4;
static const lean_string_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "titleString"};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7;
static const lean_string_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "metadata"};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__8 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__8_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9_value;
static const lean_string_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "content"};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__10 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__10_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12;
static const lean_string_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "subParts"};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__13 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__13_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__1 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__2 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value)}};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sections"};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__4 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5_value;
static const lean_string_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "declarationRange"};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__6 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__6_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__6_value)}};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7_value;
static lean_once_cell_t l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_VersoModuleDocs_instReprSnippet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_VersoModuleDocs_instReprSnippet = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoModuleDocs_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoModuleDocs;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprVersoModuleDocs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "snippets := "};
static const lean_object* l_Lean_instReprVersoModuleDocs___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprVersoModuleDocs___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instReprVersoModuleDocs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprVersoModuleDocs___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instReprVersoModuleDocs___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprVersoModuleDocs___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instReprVersoModuleDocs___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprVersoModuleDocs___lam__0___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprVersoModuleDocs___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprVersoModuleDocs___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprVersoModuleDocs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprVersoModuleDocs___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet___closed__0_value)} };
static const lean_object* l_Lean_instReprVersoModuleDocs___closed__0 = (const lean_object*)&l_Lean_instReprVersoModuleDocs___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprVersoModuleDocs = (const lean_object*)&l_Lean_instReprVersoModuleDocs___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_VersoModuleDocs_add___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Can't nest this snippet here"};
static const lean_object* l_Lean_VersoModuleDocs_add___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_add___closed__0_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_add___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_add___closed__0_value)}};
static const lean_object* l_Lean_VersoModuleDocs_add___closed__1 = (const lean_object*)&l_Lean_VersoModuleDocs_add___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_VersoModuleDocs_add_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.DocString.Extension"};
static const lean_object* l_Lean_VersoModuleDocs_add_x21___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_add_x21___closed__0_value;
static const lean_string_object l_Lean_VersoModuleDocs_add_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.VersoModuleDocs.add!"};
static const lean_object* l_Lean_VersoModuleDocs_add_x21___closed__1 = (const lean_object*)&l_Lean_VersoModuleDocs_add_x21___closed__1_value;
static lean_once_cell_t l_Lean_VersoModuleDocs_add_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_VersoModuleDocs_add_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Can't close a section: none are open"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__0 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object*);
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Invalid nesting: expected at most "};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " but got "};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Can't add content after sub-parts"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__0 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_VersoModuleDocs_assemble___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value),((lean_object*)&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value),((lean_object*)&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value)}};
static const lean_object* l_Lean_VersoModuleDocs_assemble___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_assemble___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_VersoModuleDocs_add_x21, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "versoModuleDocExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 74, 101, 232, 220, 166, 152, 230)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object*);
static lean_once_cell_t l_Lean_getVersoModuleDoc_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getVersoModuleDoc_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModuleDocSnippet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Can't add - incorrect nesting "};
static const lean_object* l_Lean_addVersoModuleDocSnippet___closed__0 = (const lean_object*)&l_Lean_addVersoModuleDocSnippet___closed__0_value;
static const lean_string_object l_Lean_addVersoModuleDocSnippet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "(expected at most "};
static const lean_object* l_Lean_addVersoModuleDocSnippet___closed__1 = (const lean_object*)&l_Lean_addVersoModuleDocSnippet___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0(lean_object* v_v_16_, lean_object* v_x_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_18_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__5));
v___x_19_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_v_16_);
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = l_Lean_Name_reprPrec(v___x_19_, v___x_20_);
v___x_22_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_22_, 0, v___x_18_);
lean_ctor_set(v___x_22_, 1, v___x_21_);
v___x_23_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__7));
v___x_24_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_22_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
v___x_25_ = l_Std_Format_nestD(v___x_24_);
v___x_26_ = 0;
v___x_27_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_27_, 0, v___x_25_);
lean_ctor_set_uint8(v___x_27_, sizeof(void*)*1, v___x_26_);
v___x_28_ = l_Std_Format_nestD(v___x_27_);
v___x_29_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set_uint8(v___x_29_, sizeof(void*)*1, v___x_26_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0___boxed(lean_object* v_v_30_, lean_object* v_x_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_instReprElabInline___lam__0(v_v_30_, v_x_31_);
lean_dec(v_x_31_);
lean_dec(v_v_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object* v_name_42_, lean_object* v_decl_43_, lean_object* v_ref_44_){
_start:
{
lean_object* v_defValue_46_; lean_object* v_descr_47_; lean_object* v_deprecation_x3f_48_; lean_object* v___x_49_; uint8_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_defValue_46_ = lean_ctor_get(v_decl_43_, 0);
v_descr_47_ = lean_ctor_get(v_decl_43_, 1);
v_deprecation_x3f_48_ = lean_ctor_get(v_decl_43_, 2);
v___x_49_ = lean_alloc_ctor(1, 0, 1);
v___x_50_ = lean_unbox(v_defValue_46_);
lean_ctor_set_uint8(v___x_49_, 0, v___x_50_);
lean_inc(v_deprecation_x3f_48_);
lean_inc_ref(v_descr_47_);
lean_inc_n(v_name_42_, 2);
v___x_51_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_51_, 0, v_name_42_);
lean_ctor_set(v___x_51_, 1, v_ref_44_);
lean_ctor_set(v___x_51_, 2, v___x_49_);
lean_ctor_set(v___x_51_, 3, v_descr_47_);
lean_ctor_set(v___x_51_, 4, v_deprecation_x3f_48_);
v___x_52_ = lean_register_option(v_name_42_, v___x_51_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_60_; 
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_60_ == 0)
{
lean_object* v_unused_61_; 
v_unused_61_ = lean_ctor_get(v___x_52_, 0);
lean_dec(v_unused_61_);
v___x_54_ = v___x_52_;
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
else
{
lean_dec(v___x_52_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_58_; 
lean_inc(v_defValue_46_);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v_name_42_);
lean_ctor_set(v___x_56_, 1, v_defValue_46_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_56_);
v___x_58_ = v___x_54_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
lean_dec(v_name_42_);
v_a_62_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_52_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_52_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_70_, lean_object* v_decl_71_, lean_object* v_ref_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v_name_70_, v_decl_71_, v_ref_72_);
lean_dec_ref(v_decl_71_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_93_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_94_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_95_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_92_, v___x_93_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_115_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_116_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_117_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_118_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_115_, v___x_116_, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_box(1);
v___x_123_ = lean_st_mk_ref(v___x_122_);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v_k_129_; lean_object* v_v_130_; lean_object* v_l_131_; lean_object* v_r_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_k_129_ = lean_ctor_get(v_x_128_, 1);
v_v_130_ = lean_ctor_get(v_x_128_, 2);
v_l_131_ = lean_ctor_get(v_x_128_, 3);
v_r_132_ = lean_ctor_get(v_x_128_, 4);
v___x_133_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_127_, v_l_131_);
lean_inc(v_v_130_);
lean_inc(v_k_129_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_k_129_);
lean_ctor_set(v___x_134_, 1, v_v_130_);
v___x_135_ = lean_array_push(v___x_133_, v___x_134_);
v_init_127_ = v___x_135_;
v_x_128_ = v_r_132_;
goto _start;
}
else
{
return v_init_127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_137_, lean_object* v_x_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_137_, v_x_138_);
lean_dec(v_x_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(lean_object* v_x_144_, lean_object* v_s_145_){
_start:
{
lean_object* v___x_146_; lean_object* v_ents_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v_ents_147_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v___x_146_, v_s_145_);
v___x_148_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
lean_inc_ref(v_ents_147_);
v___x_149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_ents_147_);
lean_ctor_set(v___x_149_, 2, v_ents_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_x_150_, lean_object* v_s_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(v_x_150_, v_s_151_);
lean_dec(v_s_151_);
lean_dec_ref(v_x_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___f_161_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_162_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_163_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_164_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_162_, v___x_163_, v___f_161_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(lean_object* v_init_167_, lean_object* v_t_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_167_, v_t_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_170_, lean_object* v_t_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(v_init_170_, v_t_171_);
lean_dec(v_t_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v_k_175_; lean_object* v_v_176_; lean_object* v_l_177_; lean_object* v_r_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_k_175_ = lean_ctor_get(v_x_174_, 1);
v_v_176_ = lean_ctor_get(v_x_174_, 2);
v_l_177_ = lean_ctor_get(v_x_174_, 3);
v_r_178_ = lean_ctor_get(v_x_174_, 4);
v___x_179_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_173_, v_l_177_);
lean_inc(v_v_176_);
lean_inc(v_k_175_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_k_175_);
lean_ctor_set(v___x_180_, 1, v_v_176_);
v___x_181_ = lean_array_push(v___x_179_, v___x_180_);
v_init_173_ = v___x_181_;
v_x_174_ = v_r_178_;
goto _start;
}
else
{
return v_init_173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_183_, lean_object* v_x_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_183_, v_x_184_);
lean_dec(v_x_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(lean_object* v_x_190_, lean_object* v_s_191_){
_start:
{
lean_object* v___x_192_; lean_object* v_ents_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_192_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v_ents_193_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v___x_192_, v_s_191_);
v___x_194_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
lean_inc_ref(v_ents_193_);
v___x_195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_ents_193_);
lean_ctor_set(v___x_195_, 2, v_ents_193_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_x_196_, lean_object* v_s_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(v_x_196_, v_s_197_);
lean_dec(v_s_197_);
lean_dec_ref(v_x_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___f_228_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_229_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_230_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_231_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_229_, v___x_230_, v___f_228_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_();
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(lean_object* v_init_234_, lean_object* v_t_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_234_, v_t_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_237_, lean_object* v_t_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(v_init_237_, v_t_238_);
lean_dec(v_t_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_box(1);
v___x_242_ = lean_st_mk_ref(v___x_241_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
lean_object* v_k_248_; lean_object* v_v_249_; lean_object* v_l_250_; lean_object* v_r_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_k_248_ = lean_ctor_get(v_x_247_, 1);
v_v_249_ = lean_ctor_get(v_x_247_, 2);
v_l_250_ = lean_ctor_get(v_x_247_, 3);
v_r_251_ = lean_ctor_get(v_x_247_, 4);
v___x_252_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_246_, v_l_250_);
lean_inc(v_v_249_);
lean_inc(v_k_248_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_k_248_);
lean_ctor_set(v___x_253_, 1, v_v_249_);
v___x_254_ = lean_array_push(v___x_252_, v___x_253_);
v_init_246_ = v___x_254_;
v_x_247_ = v_r_251_;
goto _start;
}
else
{
return v_init_246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_256_, lean_object* v_x_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_256_, v_x_257_);
lean_dec(v_x_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(lean_object* v_x_263_, lean_object* v_s_264_){
_start:
{
lean_object* v___x_265_; lean_object* v_ents_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v_ents_266_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v___x_265_, v_s_264_);
v___x_267_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
lean_inc_ref(v_ents_266_);
v___x_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v_ents_266_);
lean_ctor_set(v___x_268_, 2, v_ents_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_x_269_, lean_object* v_s_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(v_x_269_, v_s_270_);
lean_dec(v_s_270_);
lean_dec_ref(v_x_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___f_278_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_279_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_280_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_281_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_279_, v___x_280_, v___f_278_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(lean_object* v_init_284_, lean_object* v_t_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_284_, v_t_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_287_, lean_object* v_t_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(v_init_287_, v_t_288_);
lean_dec(v_t_288_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString(lean_object* v_declName_290_, lean_object* v_docString_291_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_293_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_294_ = lean_st_ref_take(v___x_293_);
v___x_295_ = l_String_removeLeadingSpaces(v_docString_291_);
v___x_296_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_290_, v___x_295_, v___x_294_);
v___x_297_ = lean_st_ref_set(v___x_293_, v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString___boxed(lean_object* v_declName_299_, lean_object* v_docString_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_addBuiltinDocString(v_declName_299_, v_docString_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object* v_k_303_, lean_object* v_t_304_){
_start:
{
if (lean_obj_tag(v_t_304_) == 0)
{
lean_object* v_k_305_; lean_object* v_v_306_; lean_object* v_l_307_; lean_object* v_r_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_962_; 
v_k_305_ = lean_ctor_get(v_t_304_, 1);
v_v_306_ = lean_ctor_get(v_t_304_, 2);
v_l_307_ = lean_ctor_get(v_t_304_, 3);
v_r_308_ = lean_ctor_get(v_t_304_, 4);
v_isSharedCheck_962_ = !lean_is_exclusive(v_t_304_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_t_304_, 0);
lean_dec(v_unused_963_);
v___x_310_ = v_t_304_;
v_isShared_311_ = v_isSharedCheck_962_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_r_308_);
lean_inc(v_l_307_);
lean_inc(v_v_306_);
lean_inc(v_k_305_);
lean_dec(v_t_304_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_962_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint8_t v___x_312_; 
v___x_312_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_303_, v_k_305_);
switch(v___x_312_)
{
case 0:
{
lean_object* v_impl_313_; lean_object* v___x_314_; 
v_impl_313_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_303_, v_l_307_);
v___x_314_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_313_) == 0)
{
if (lean_obj_tag(v_r_308_) == 0)
{
lean_object* v_size_315_; lean_object* v_size_316_; lean_object* v_k_317_; lean_object* v_v_318_; lean_object* v_l_319_; lean_object* v_r_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_size_315_ = lean_ctor_get(v_impl_313_, 0);
lean_inc(v_size_315_);
v_size_316_ = lean_ctor_get(v_r_308_, 0);
v_k_317_ = lean_ctor_get(v_r_308_, 1);
v_v_318_ = lean_ctor_get(v_r_308_, 2);
v_l_319_ = lean_ctor_get(v_r_308_, 3);
lean_inc(v_l_319_);
v_r_320_ = lean_ctor_get(v_r_308_, 4);
v___x_321_ = lean_unsigned_to_nat(3u);
v___x_322_ = lean_nat_mul(v___x_321_, v_size_315_);
v___x_323_ = lean_nat_dec_lt(v___x_322_, v_size_316_);
lean_dec(v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
lean_dec(v_l_319_);
v___x_324_ = lean_nat_add(v___x_314_, v_size_315_);
lean_dec(v_size_315_);
v___x_325_ = lean_nat_add(v___x_324_, v_size_316_);
lean_dec(v___x_324_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 3, v_impl_313_);
lean_ctor_set(v___x_310_, 0, v___x_325_);
v___x_327_ = v___x_310_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_328_, 3, v_impl_313_);
lean_ctor_set(v_reuseFailAlloc_328_, 4, v_r_308_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
else
{
lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_392_; 
lean_inc(v_r_320_);
lean_inc(v_v_318_);
lean_inc(v_k_317_);
lean_inc(v_size_316_);
v_isSharedCheck_392_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; lean_object* v_unused_394_; lean_object* v_unused_395_; lean_object* v_unused_396_; lean_object* v_unused_397_; 
v_unused_393_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_393_);
v_unused_394_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_394_);
v_unused_395_ = lean_ctor_get(v_r_308_, 2);
lean_dec(v_unused_395_);
v_unused_396_ = lean_ctor_get(v_r_308_, 1);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_397_);
v___x_330_ = v_r_308_;
v_isShared_331_ = v_isSharedCheck_392_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_r_308_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_392_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v_size_332_; lean_object* v_k_333_; lean_object* v_v_334_; lean_object* v_l_335_; lean_object* v_r_336_; lean_object* v_size_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_size_332_ = lean_ctor_get(v_l_319_, 0);
v_k_333_ = lean_ctor_get(v_l_319_, 1);
v_v_334_ = lean_ctor_get(v_l_319_, 2);
v_l_335_ = lean_ctor_get(v_l_319_, 3);
v_r_336_ = lean_ctor_get(v_l_319_, 4);
v_size_337_ = lean_ctor_get(v_r_320_, 0);
v___x_338_ = lean_unsigned_to_nat(2u);
v___x_339_ = lean_nat_mul(v___x_338_, v_size_337_);
v___x_340_ = lean_nat_dec_lt(v_size_332_, v___x_339_);
lean_dec(v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_368_; 
lean_inc(v_r_336_);
lean_inc(v_l_335_);
lean_inc(v_v_334_);
lean_inc(v_k_333_);
v_isSharedCheck_368_ = !lean_is_exclusive(v_l_319_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; lean_object* v_unused_371_; lean_object* v_unused_372_; lean_object* v_unused_373_; 
v_unused_369_ = lean_ctor_get(v_l_319_, 4);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_l_319_, 3);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_l_319_, 2);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v_l_319_, 1);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_l_319_, 0);
lean_dec(v_unused_373_);
v___x_342_ = v_l_319_;
v_isShared_343_ = v_isSharedCheck_368_;
goto v_resetjp_341_;
}
else
{
lean_dec(v_l_319_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_368_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_358_; 
v___x_344_ = lean_nat_add(v___x_314_, v_size_315_);
lean_dec(v_size_315_);
v___x_345_ = lean_nat_add(v___x_344_, v_size_316_);
lean_dec(v_size_316_);
if (lean_obj_tag(v_l_335_) == 0)
{
lean_object* v_size_366_; 
v_size_366_ = lean_ctor_get(v_l_335_, 0);
lean_inc(v_size_366_);
v___y_358_ = v_size_366_;
goto v___jp_357_;
}
else
{
lean_object* v___x_367_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v___y_358_ = v___x_367_;
goto v___jp_357_;
}
v___jp_346_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_nat_add(v___y_347_, v___y_349_);
lean_dec(v___y_349_);
lean_dec(v___y_347_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v_r_320_);
lean_ctor_set(v___x_342_, 3, v_r_336_);
lean_ctor_set(v___x_342_, 2, v_v_318_);
lean_ctor_set(v___x_342_, 1, v_k_317_);
lean_ctor_set(v___x_342_, 0, v___x_350_);
v___x_352_ = v___x_342_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_k_317_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_v_318_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_r_336_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v_r_320_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_354_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 4, v___x_352_);
lean_ctor_set(v___x_330_, 3, v___y_348_);
lean_ctor_set(v___x_330_, 2, v_v_334_);
lean_ctor_set(v___x_330_, 1, v_k_333_);
lean_ctor_set(v___x_330_, 0, v___x_345_);
v___x_354_ = v___x_330_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_k_333_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_v_334_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v___y_348_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
v___jp_357_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_nat_add(v___x_344_, v___y_358_);
lean_dec(v___y_358_);
lean_dec(v___x_344_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_l_335_);
lean_ctor_set(v___x_310_, 3, v_impl_313_);
lean_ctor_set(v___x_310_, 0, v___x_359_);
v___x_361_ = v___x_310_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_impl_313_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_l_335_);
v___x_361_ = v_reuseFailAlloc_365_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; 
v___x_362_ = lean_nat_add(v___x_314_, v_size_337_);
if (lean_obj_tag(v_r_336_) == 0)
{
lean_object* v_size_363_; 
v_size_363_ = lean_ctor_get(v_r_336_, 0);
lean_inc(v_size_363_);
v___y_347_ = v___x_362_;
v___y_348_ = v___x_361_;
v___y_349_ = v_size_363_;
goto v___jp_346_;
}
else
{
lean_object* v___x_364_; 
v___x_364_ = lean_unsigned_to_nat(0u);
v___y_347_ = v___x_362_;
v___y_348_ = v___x_361_;
v___y_349_ = v___x_364_;
goto v___jp_346_;
}
}
}
}
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
lean_del_object(v___x_310_);
v___x_374_ = lean_nat_add(v___x_314_, v_size_315_);
lean_dec(v_size_315_);
v___x_375_ = lean_nat_add(v___x_374_, v_size_316_);
lean_dec(v_size_316_);
v___x_376_ = lean_nat_add(v___x_374_, v_size_332_);
lean_dec(v___x_374_);
lean_inc_ref(v_impl_313_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 4, v_l_319_);
lean_ctor_set(v___x_330_, 3, v_impl_313_);
lean_ctor_set(v___x_330_, 2, v_v_306_);
lean_ctor_set(v___x_330_, 1, v_k_305_);
lean_ctor_set(v___x_330_, 0, v___x_376_);
v___x_378_ = v___x_330_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_impl_313_);
lean_ctor_set(v_reuseFailAlloc_391_, 4, v_l_319_);
v___x_378_ = v_reuseFailAlloc_391_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
v_isSharedCheck_385_ = !lean_is_exclusive(v_impl_313_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; lean_object* v_unused_387_; lean_object* v_unused_388_; lean_object* v_unused_389_; lean_object* v_unused_390_; 
v_unused_386_ = lean_ctor_get(v_impl_313_, 4);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_impl_313_, 3);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_impl_313_, 2);
lean_dec(v_unused_388_);
v_unused_389_ = lean_ctor_get(v_impl_313_, 1);
lean_dec(v_unused_389_);
v_unused_390_ = lean_ctor_get(v_impl_313_, 0);
lean_dec(v_unused_390_);
v___x_380_ = v_impl_313_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_dec(v_impl_313_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 4, v_r_320_);
lean_ctor_set(v___x_380_, 3, v___x_378_);
lean_ctor_set(v___x_380_, 2, v_v_318_);
lean_ctor_set(v___x_380_, 1, v_k_317_);
lean_ctor_set(v___x_380_, 0, v___x_375_);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_k_317_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v_v_318_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v_r_320_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v_size_398_ = lean_ctor_get(v_impl_313_, 0);
lean_inc(v_size_398_);
v___x_399_ = lean_nat_add(v___x_314_, v_size_398_);
lean_dec(v_size_398_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 3, v_impl_313_);
lean_ctor_set(v___x_310_, 0, v___x_399_);
v___x_401_ = v___x_310_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_impl_313_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_r_308_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
if (lean_obj_tag(v_r_308_) == 0)
{
lean_object* v_l_403_; 
v_l_403_ = lean_ctor_get(v_r_308_, 3);
lean_inc(v_l_403_);
if (lean_obj_tag(v_l_403_) == 0)
{
lean_object* v_r_404_; 
v_r_404_ = lean_ctor_get(v_r_308_, 4);
lean_inc(v_r_404_);
if (lean_obj_tag(v_r_404_) == 0)
{
lean_object* v_size_405_; lean_object* v_k_406_; lean_object* v_v_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_420_; 
v_size_405_ = lean_ctor_get(v_r_308_, 0);
v_k_406_ = lean_ctor_get(v_r_308_, 1);
v_v_407_ = lean_ctor_get(v_r_308_, 2);
v_isSharedCheck_420_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; lean_object* v_unused_422_; 
v_unused_421_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_421_);
v_unused_422_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_422_);
v___x_409_ = v_r_308_;
v_isShared_410_ = v_isSharedCheck_420_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_v_407_);
lean_inc(v_k_406_);
lean_inc(v_size_405_);
lean_dec(v_r_308_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_420_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_size_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v_size_411_ = lean_ctor_get(v_l_403_, 0);
v___x_412_ = lean_nat_add(v___x_314_, v_size_405_);
lean_dec(v_size_405_);
v___x_413_ = lean_nat_add(v___x_314_, v_size_411_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 4, v_l_403_);
lean_ctor_set(v___x_409_, 3, v_impl_313_);
lean_ctor_set(v___x_409_, 2, v_v_306_);
lean_ctor_set(v___x_409_, 1, v_k_305_);
lean_ctor_set(v___x_409_, 0, v___x_413_);
v___x_415_ = v___x_409_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_419_, 3, v_impl_313_);
lean_ctor_set(v_reuseFailAlloc_419_, 4, v_l_403_);
v___x_415_ = v_reuseFailAlloc_419_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_417_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_r_404_);
lean_ctor_set(v___x_310_, 3, v___x_415_);
lean_ctor_set(v___x_310_, 2, v_v_407_);
lean_ctor_set(v___x_310_, 1, v_k_406_);
lean_ctor_set(v___x_310_, 0, v___x_412_);
v___x_417_ = v___x_310_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_k_406_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_v_407_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_r_404_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v_k_423_; lean_object* v_v_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_447_; 
v_k_423_ = lean_ctor_get(v_r_308_, 1);
v_v_424_ = lean_ctor_get(v_r_308_, 2);
v_isSharedCheck_447_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_448_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_450_);
v___x_426_ = v_r_308_;
v_isShared_427_ = v_isSharedCheck_447_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_v_424_);
lean_inc(v_k_423_);
lean_dec(v_r_308_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_447_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_k_428_; lean_object* v_v_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_443_; 
v_k_428_ = lean_ctor_get(v_l_403_, 1);
v_v_429_ = lean_ctor_get(v_l_403_, 2);
v_isSharedCheck_443_ = !lean_is_exclusive(v_l_403_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_444_ = lean_ctor_get(v_l_403_, 4);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_l_403_, 3);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_l_403_, 0);
lean_dec(v_unused_446_);
v___x_431_ = v_l_403_;
v_isShared_432_ = v_isSharedCheck_443_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_v_429_);
lean_inc(v_k_428_);
lean_dec(v_l_403_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_443_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_unsigned_to_nat(3u);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 4, v_r_404_);
lean_ctor_set(v___x_431_, 3, v_r_404_);
lean_ctor_set(v___x_431_, 2, v_v_306_);
lean_ctor_set(v___x_431_, 1, v_k_305_);
lean_ctor_set(v___x_431_, 0, v___x_314_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v_r_404_);
lean_ctor_set(v_reuseFailAlloc_442_, 4, v_r_404_);
v___x_435_ = v_reuseFailAlloc_442_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_437_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 3, v_r_404_);
lean_ctor_set(v___x_426_, 0, v___x_314_);
v___x_437_ = v___x_426_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_k_423_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_v_424_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_r_404_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v_r_404_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v___x_437_);
lean_ctor_set(v___x_310_, 3, v___x_435_);
lean_ctor_set(v___x_310_, 2, v_v_429_);
lean_ctor_set(v___x_310_, 1, v_k_428_);
lean_ctor_set(v___x_310_, 0, v___x_433_);
v___x_439_ = v___x_310_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_k_428_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_v_429_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_451_; 
v_r_451_ = lean_ctor_get(v_r_308_, 4);
lean_inc(v_r_451_);
if (lean_obj_tag(v_r_451_) == 0)
{
lean_object* v_k_452_; lean_object* v_v_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_464_; 
v_k_452_ = lean_ctor_get(v_r_308_, 1);
v_v_453_ = lean_ctor_get(v_r_308_, 2);
v_isSharedCheck_464_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_465_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_467_);
v___x_455_ = v_r_308_;
v_isShared_456_ = v_isSharedCheck_464_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_v_453_);
lean_inc(v_k_452_);
lean_dec(v_r_308_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_464_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = lean_unsigned_to_nat(3u);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_l_403_);
lean_ctor_set(v___x_455_, 2, v_v_306_);
lean_ctor_set(v___x_455_, 1, v_k_305_);
lean_ctor_set(v___x_455_, 0, v___x_314_);
v___x_459_ = v___x_455_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_l_403_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_l_403_);
v___x_459_ = v_reuseFailAlloc_463_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_461_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_r_451_);
lean_ctor_set(v___x_310_, 3, v___x_459_);
lean_ctor_set(v___x_310_, 2, v_v_453_);
lean_ctor_set(v___x_310_, 1, v_k_452_);
lean_ctor_set(v___x_310_, 0, v___x_457_);
v___x_461_ = v___x_310_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_k_452_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_v_453_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_462_, 4, v_r_451_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v_size_468_; lean_object* v_k_469_; lean_object* v_v_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_481_; 
v_size_468_ = lean_ctor_get(v_r_308_, 0);
v_k_469_ = lean_ctor_get(v_r_308_, 1);
v_v_470_ = lean_ctor_get(v_r_308_, 2);
v_isSharedCheck_481_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; lean_object* v_unused_483_; 
v_unused_482_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_483_);
v___x_472_ = v_r_308_;
v_isShared_473_ = v_isSharedCheck_481_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_v_470_);
lean_inc(v_k_469_);
lean_inc(v_size_468_);
lean_dec(v_r_308_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_481_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 3, v_r_451_);
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_size_468_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_k_469_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_v_470_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_r_451_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_r_451_);
v___x_475_ = v_reuseFailAlloc_480_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_unsigned_to_nat(2u);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v___x_475_);
lean_ctor_set(v___x_310_, 3, v_r_451_);
lean_ctor_set(v___x_310_, 0, v___x_476_);
v___x_478_ = v___x_310_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_r_451_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v___x_475_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
else
{
lean_object* v___x_485_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 3, v_r_308_);
lean_ctor_set(v___x_310_, 0, v___x_314_);
v___x_485_ = v___x_310_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v_r_308_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v_r_308_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
case 1:
{
lean_del_object(v___x_310_);
lean_dec(v_v_306_);
lean_dec(v_k_305_);
if (lean_obj_tag(v_l_307_) == 0)
{
if (lean_obj_tag(v_r_308_) == 0)
{
lean_object* v_size_487_; lean_object* v_k_488_; lean_object* v_v_489_; lean_object* v_l_490_; lean_object* v_r_491_; lean_object* v_size_492_; lean_object* v_k_493_; lean_object* v_v_494_; lean_object* v_l_495_; lean_object* v_r_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_size_487_ = lean_ctor_get(v_l_307_, 0);
v_k_488_ = lean_ctor_get(v_l_307_, 1);
v_v_489_ = lean_ctor_get(v_l_307_, 2);
v_l_490_ = lean_ctor_get(v_l_307_, 3);
v_r_491_ = lean_ctor_get(v_l_307_, 4);
lean_inc(v_r_491_);
v_size_492_ = lean_ctor_get(v_r_308_, 0);
v_k_493_ = lean_ctor_get(v_r_308_, 1);
v_v_494_ = lean_ctor_get(v_r_308_, 2);
v_l_495_ = lean_ctor_get(v_r_308_, 3);
lean_inc(v_l_495_);
v_r_496_ = lean_ctor_get(v_r_308_, 4);
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = lean_nat_dec_lt(v_size_487_, v_size_492_);
if (v___x_498_ == 0)
{
lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_634_; 
lean_inc(v_l_490_);
lean_inc(v_v_489_);
lean_inc(v_k_488_);
v_isSharedCheck_634_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; lean_object* v_unused_636_; lean_object* v_unused_637_; lean_object* v_unused_638_; lean_object* v_unused_639_; 
v_unused_635_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_l_307_, 2);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_l_307_, 1);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_639_);
v___x_500_ = v_l_307_;
v_isShared_501_ = v_isSharedCheck_634_;
goto v_resetjp_499_;
}
else
{
lean_dec(v_l_307_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_634_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v_tree_503_; 
v___x_502_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_488_, v_v_489_, v_l_490_, v_r_491_);
v_tree_503_ = lean_ctor_get(v___x_502_, 2);
lean_inc(v_tree_503_);
if (lean_obj_tag(v_tree_503_) == 0)
{
lean_object* v_k_504_; lean_object* v_v_505_; lean_object* v_size_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_k_504_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_k_504_);
v_v_505_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_v_505_);
lean_dec_ref(v___x_502_);
v_size_506_ = lean_ctor_get(v_tree_503_, 0);
v___x_507_ = lean_unsigned_to_nat(3u);
v___x_508_ = lean_nat_mul(v___x_507_, v_size_506_);
v___x_509_ = lean_nat_dec_lt(v___x_508_, v_size_492_);
lean_dec(v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
lean_dec(v_l_495_);
v___x_510_ = lean_nat_add(v___x_497_, v_size_506_);
v___x_511_ = lean_nat_add(v___x_510_, v_size_492_);
lean_dec(v___x_510_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_r_308_);
lean_ctor_set(v___x_500_, 3, v_tree_503_);
lean_ctor_set(v___x_500_, 2, v_v_505_);
lean_ctor_set(v___x_500_, 1, v_k_504_);
lean_ctor_set(v___x_500_, 0, v___x_511_);
v___x_513_ = v___x_500_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_k_504_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_v_505_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_tree_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_r_308_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_569_; 
lean_inc(v_r_496_);
lean_inc(v_v_494_);
lean_inc(v_k_493_);
lean_inc(v_size_492_);
v_isSharedCheck_569_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; 
v_unused_570_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_r_308_, 2);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_r_308_, 1);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_574_);
v___x_516_ = v_r_308_;
v_isShared_517_ = v_isSharedCheck_569_;
goto v_resetjp_515_;
}
else
{
lean_dec(v_r_308_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_569_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_size_518_; lean_object* v_k_519_; lean_object* v_v_520_; lean_object* v_l_521_; lean_object* v_r_522_; lean_object* v_size_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_size_518_ = lean_ctor_get(v_l_495_, 0);
v_k_519_ = lean_ctor_get(v_l_495_, 1);
v_v_520_ = lean_ctor_get(v_l_495_, 2);
v_l_521_ = lean_ctor_get(v_l_495_, 3);
v_r_522_ = lean_ctor_get(v_l_495_, 4);
v_size_523_ = lean_ctor_get(v_r_496_, 0);
v___x_524_ = lean_unsigned_to_nat(2u);
v___x_525_ = lean_nat_mul(v___x_524_, v_size_523_);
v___x_526_ = lean_nat_dec_lt(v_size_518_, v___x_525_);
lean_dec(v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_554_; 
lean_inc(v_r_522_);
lean_inc(v_l_521_);
lean_inc(v_v_520_);
lean_inc(v_k_519_);
v_isSharedCheck_554_ = !lean_is_exclusive(v_l_495_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_555_ = lean_ctor_get(v_l_495_, 4);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_l_495_, 3);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_l_495_, 2);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_l_495_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_l_495_, 0);
lean_dec(v_unused_559_);
v___x_528_ = v_l_495_;
v_isShared_529_ = v_isSharedCheck_554_;
goto v_resetjp_527_;
}
else
{
lean_dec(v_l_495_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_554_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_544_; 
v___x_530_ = lean_nat_add(v___x_497_, v_size_506_);
v___x_531_ = lean_nat_add(v___x_530_, v_size_492_);
lean_dec(v_size_492_);
if (lean_obj_tag(v_l_521_) == 0)
{
lean_object* v_size_552_; 
v_size_552_ = lean_ctor_get(v_l_521_, 0);
lean_inc(v_size_552_);
v___y_544_ = v_size_552_;
goto v___jp_543_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v___y_544_ = v___x_553_;
goto v___jp_543_;
}
v___jp_532_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_nat_add(v___y_533_, v___y_535_);
lean_dec(v___y_535_);
lean_dec(v___y_533_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 4, v_r_496_);
lean_ctor_set(v___x_528_, 3, v_r_522_);
lean_ctor_set(v___x_528_, 2, v_v_494_);
lean_ctor_set(v___x_528_, 1, v_k_493_);
lean_ctor_set(v___x_528_, 0, v___x_536_);
v___x_538_ = v___x_528_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_r_522_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_r_496_);
v___x_538_ = v_reuseFailAlloc_542_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_540_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 4, v___x_538_);
lean_ctor_set(v___x_516_, 3, v___y_534_);
lean_ctor_set(v___x_516_, 2, v_v_520_);
lean_ctor_set(v___x_516_, 1, v_k_519_);
lean_ctor_set(v___x_516_, 0, v___x_531_);
v___x_540_ = v___x_516_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_k_519_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_v_520_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v___y_534_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_nat_add(v___x_530_, v___y_544_);
lean_dec(v___y_544_);
lean_dec(v___x_530_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_l_521_);
lean_ctor_set(v___x_500_, 3, v_tree_503_);
lean_ctor_set(v___x_500_, 2, v_v_505_);
lean_ctor_set(v___x_500_, 1, v_k_504_);
lean_ctor_set(v___x_500_, 0, v___x_545_);
v___x_547_ = v___x_500_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_k_504_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_v_505_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_tree_503_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v_l_521_);
v___x_547_ = v_reuseFailAlloc_551_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; 
v___x_548_ = lean_nat_add(v___x_497_, v_size_523_);
if (lean_obj_tag(v_r_522_) == 0)
{
lean_object* v_size_549_; 
v_size_549_ = lean_ctor_get(v_r_522_, 0);
lean_inc(v_size_549_);
v___y_533_ = v___x_548_;
v___y_534_ = v___x_547_;
v___y_535_ = v_size_549_;
goto v___jp_532_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___y_533_ = v___x_548_;
v___y_534_ = v___x_547_;
v___y_535_ = v___x_550_;
goto v___jp_532_;
}
}
}
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_560_ = lean_nat_add(v___x_497_, v_size_506_);
v___x_561_ = lean_nat_add(v___x_560_, v_size_492_);
lean_dec(v_size_492_);
v___x_562_ = lean_nat_add(v___x_560_, v_size_518_);
lean_dec(v___x_560_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 4, v_l_495_);
lean_ctor_set(v___x_516_, 3, v_tree_503_);
lean_ctor_set(v___x_516_, 2, v_v_505_);
lean_ctor_set(v___x_516_, 1, v_k_504_);
lean_ctor_set(v___x_516_, 0, v___x_562_);
v___x_564_ = v___x_516_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_k_504_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_v_505_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_tree_503_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_l_495_);
v___x_564_ = v_reuseFailAlloc_568_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_r_496_);
lean_ctor_set(v___x_500_, 3, v___x_564_);
lean_ctor_set(v___x_500_, 2, v_v_494_);
lean_ctor_set(v___x_500_, 1, v_k_493_);
lean_ctor_set(v___x_500_, 0, v___x_561_);
v___x_566_ = v___x_500_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_r_496_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
}
else
{
lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_628_; 
lean_inc(v_r_496_);
lean_inc(v_v_494_);
lean_inc(v_k_493_);
lean_inc(v_size_492_);
v_isSharedCheck_628_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; lean_object* v_unused_630_; lean_object* v_unused_631_; lean_object* v_unused_632_; lean_object* v_unused_633_; 
v_unused_629_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_r_308_, 2);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_r_308_, 1);
lean_dec(v_unused_632_);
v_unused_633_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_633_);
v___x_576_ = v_r_308_;
v_isShared_577_ = v_isSharedCheck_628_;
goto v_resetjp_575_;
}
else
{
lean_dec(v_r_308_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_628_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
if (lean_obj_tag(v_l_495_) == 0)
{
if (lean_obj_tag(v_r_496_) == 0)
{
lean_object* v_k_578_; lean_object* v_v_579_; lean_object* v_size_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
v_k_578_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_k_578_);
v_v_579_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_v_579_);
lean_dec_ref(v___x_502_);
v_size_580_ = lean_ctor_get(v_l_495_, 0);
v___x_581_ = lean_nat_add(v___x_497_, v_size_492_);
lean_dec(v_size_492_);
v___x_582_ = lean_nat_add(v___x_497_, v_size_580_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 4, v_l_495_);
lean_ctor_set(v___x_576_, 3, v_tree_503_);
lean_ctor_set(v___x_576_, 2, v_v_579_);
lean_ctor_set(v___x_576_, 1, v_k_578_);
lean_ctor_set(v___x_576_, 0, v___x_582_);
v___x_584_ = v___x_576_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_k_578_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_v_579_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_tree_503_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v_l_495_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_r_496_);
lean_ctor_set(v___x_500_, 3, v___x_584_);
lean_ctor_set(v___x_500_, 2, v_v_494_);
lean_ctor_set(v___x_500_, 1, v_k_493_);
lean_ctor_set(v___x_500_, 0, v___x_581_);
v___x_586_ = v___x_500_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v_r_496_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_k_589_; lean_object* v_v_590_; lean_object* v_k_591_; lean_object* v_v_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_size_492_);
v_k_589_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_k_589_);
v_v_590_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_v_590_);
lean_dec_ref(v___x_502_);
v_k_591_ = lean_ctor_get(v_l_495_, 1);
v_v_592_ = lean_ctor_get(v_l_495_, 2);
v_isSharedCheck_606_ = !lean_is_exclusive(v_l_495_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; lean_object* v_unused_608_; lean_object* v_unused_609_; 
v_unused_607_ = lean_ctor_get(v_l_495_, 4);
lean_dec(v_unused_607_);
v_unused_608_ = lean_ctor_get(v_l_495_, 3);
lean_dec(v_unused_608_);
v_unused_609_ = lean_ctor_get(v_l_495_, 0);
lean_dec(v_unused_609_);
v___x_594_ = v_l_495_;
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_v_592_);
lean_inc(v_k_591_);
lean_dec(v_l_495_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_unsigned_to_nat(3u);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v_r_496_);
lean_ctor_set(v___x_594_, 3, v_r_496_);
lean_ctor_set(v___x_594_, 2, v_v_590_);
lean_ctor_set(v___x_594_, 1, v_k_589_);
lean_ctor_set(v___x_594_, 0, v___x_497_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_r_496_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_r_496_);
v___x_598_ = v_reuseFailAlloc_605_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 3, v_r_496_);
lean_ctor_set(v___x_576_, 0, v___x_497_);
v___x_600_ = v___x_576_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_r_496_);
lean_ctor_set(v_reuseFailAlloc_604_, 4, v_r_496_);
v___x_600_ = v_reuseFailAlloc_604_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v___x_600_);
lean_ctor_set(v___x_500_, 3, v___x_598_);
lean_ctor_set(v___x_500_, 2, v_v_592_);
lean_ctor_set(v___x_500_, 1, v_k_591_);
lean_ctor_set(v___x_500_, 0, v___x_596_);
v___x_602_ = v___x_500_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_k_591_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_v_592_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_603_, 4, v___x_600_);
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
else
{
if (lean_obj_tag(v_r_496_) == 0)
{
lean_object* v_k_610_; lean_object* v_v_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
lean_dec(v_size_492_);
v_k_610_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_k_610_);
v_v_611_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_v_611_);
lean_dec_ref(v___x_502_);
v___x_612_ = lean_unsigned_to_nat(3u);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 4, v_l_495_);
lean_ctor_set(v___x_576_, 2, v_v_611_);
lean_ctor_set(v___x_576_, 1, v_k_610_);
lean_ctor_set(v___x_576_, 0, v___x_497_);
v___x_614_ = v___x_576_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_k_610_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_v_611_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_l_495_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_l_495_);
v___x_614_ = v_reuseFailAlloc_618_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_r_496_);
lean_ctor_set(v___x_500_, 3, v___x_614_);
lean_ctor_set(v___x_500_, 2, v_v_494_);
lean_ctor_set(v___x_500_, 1, v_k_493_);
lean_ctor_set(v___x_500_, 0, v___x_612_);
v___x_616_ = v___x_500_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_r_496_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
else
{
lean_object* v_k_619_; lean_object* v_v_620_; lean_object* v___x_622_; 
v_k_619_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_k_619_);
v_v_620_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_v_620_);
lean_dec_ref(v___x_502_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 3, v_r_496_);
v___x_622_ = v___x_576_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_size_492_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_r_496_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_r_496_);
v___x_622_ = v_reuseFailAlloc_627_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_unsigned_to_nat(2u);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v___x_622_);
lean_ctor_set(v___x_500_, 3, v_r_496_);
lean_ctor_set(v___x_500_, 2, v_v_620_);
lean_ctor_set(v___x_500_, 1, v_k_619_);
lean_ctor_set(v___x_500_, 0, v___x_623_);
v___x_625_ = v___x_500_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_r_496_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v___x_622_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
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
lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_792_; 
lean_inc(v_r_496_);
lean_inc(v_v_494_);
lean_inc(v_k_493_);
v_isSharedCheck_792_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; lean_object* v_unused_794_; lean_object* v_unused_795_; lean_object* v_unused_796_; lean_object* v_unused_797_; 
v_unused_793_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_r_308_, 2);
lean_dec(v_unused_795_);
v_unused_796_ = lean_ctor_get(v_r_308_, 1);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_797_);
v___x_641_ = v_r_308_;
v_isShared_642_ = v_isSharedCheck_792_;
goto v_resetjp_640_;
}
else
{
lean_dec(v_r_308_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_792_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v_tree_644_; 
v___x_643_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_493_, v_v_494_, v_l_495_, v_r_496_);
v_tree_644_ = lean_ctor_get(v___x_643_, 2);
lean_inc(v_tree_644_);
if (lean_obj_tag(v_tree_644_) == 0)
{
lean_object* v_k_645_; lean_object* v_v_646_; lean_object* v_size_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_k_645_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_645_);
v_v_646_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_646_);
lean_dec_ref(v___x_643_);
v_size_647_ = lean_ctor_get(v_tree_644_, 0);
v___x_648_ = lean_unsigned_to_nat(3u);
v___x_649_ = lean_nat_mul(v___x_648_, v_size_647_);
v___x_650_ = lean_nat_dec_lt(v___x_649_, v_size_487_);
lean_dec(v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
lean_dec(v_r_491_);
v___x_651_ = lean_nat_add(v___x_497_, v_size_487_);
v___x_652_ = lean_nat_add(v___x_651_, v_size_647_);
lean_dec(v___x_651_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_tree_644_);
lean_ctor_set(v___x_641_, 3, v_l_307_);
lean_ctor_set(v___x_641_, 2, v_v_646_);
lean_ctor_set(v___x_641_, 1, v_k_645_);
lean_ctor_set(v___x_641_, 0, v___x_652_);
v___x_654_ = v___x_641_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v_tree_644_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
else
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_721_; 
lean_inc(v_l_490_);
lean_inc(v_v_489_);
lean_inc(v_k_488_);
lean_inc(v_size_487_);
v_isSharedCheck_721_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; lean_object* v_unused_725_; lean_object* v_unused_726_; 
v_unused_722_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_l_307_, 2);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_l_307_, 1);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_726_);
v___x_657_ = v_l_307_;
v_isShared_658_ = v_isSharedCheck_721_;
goto v_resetjp_656_;
}
else
{
lean_dec(v_l_307_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_721_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_size_659_; lean_object* v_size_660_; lean_object* v_k_661_; lean_object* v_v_662_; lean_object* v_l_663_; lean_object* v_r_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_size_659_ = lean_ctor_get(v_l_490_, 0);
v_size_660_ = lean_ctor_get(v_r_491_, 0);
v_k_661_ = lean_ctor_get(v_r_491_, 1);
v_v_662_ = lean_ctor_get(v_r_491_, 2);
v_l_663_ = lean_ctor_get(v_r_491_, 3);
v_r_664_ = lean_ctor_get(v_r_491_, 4);
v___x_665_ = lean_unsigned_to_nat(2u);
v___x_666_ = lean_nat_mul(v___x_665_, v_size_659_);
v___x_667_ = lean_nat_dec_lt(v_size_660_, v___x_666_);
lean_dec(v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_705_; 
lean_inc(v_r_664_);
lean_inc(v_l_663_);
lean_inc(v_v_662_);
lean_inc(v_k_661_);
lean_del_object(v___x_657_);
v_isSharedCheck_705_ = !lean_is_exclusive(v_r_491_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; 
v_unused_706_ = lean_ctor_get(v_r_491_, 4);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_r_491_, 3);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_r_491_, 2);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_r_491_, 1);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_r_491_, 0);
lean_dec(v_unused_710_);
v___x_669_ = v_r_491_;
v_isShared_670_ = v_isSharedCheck_705_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_r_491_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_705_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___x_693_; lean_object* v___y_695_; 
v___x_671_ = lean_nat_add(v___x_497_, v_size_487_);
lean_dec(v_size_487_);
v___x_672_ = lean_nat_add(v___x_671_, v_size_647_);
lean_dec(v___x_671_);
v___x_693_ = lean_nat_add(v___x_497_, v_size_659_);
if (lean_obj_tag(v_l_663_) == 0)
{
lean_object* v_size_703_; 
v_size_703_ = lean_ctor_get(v_l_663_, 0);
lean_inc(v_size_703_);
v___y_695_ = v_size_703_;
goto v___jp_694_;
}
else
{
lean_object* v___x_704_; 
v___x_704_ = lean_unsigned_to_nat(0u);
v___y_695_ = v___x_704_;
goto v___jp_694_;
}
v___jp_673_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_nat_add(v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec(v___y_675_);
lean_inc_ref(v_tree_644_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v_tree_644_);
lean_ctor_set(v___x_669_, 3, v_r_664_);
lean_ctor_set(v___x_669_, 2, v_v_646_);
lean_ctor_set(v___x_669_, 1, v_k_645_);
lean_ctor_set(v___x_669_, 0, v___x_677_);
v___x_679_ = v___x_669_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_r_664_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_tree_644_);
v___x_679_ = v_reuseFailAlloc_692_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
v_isSharedCheck_686_ = !lean_is_exclusive(v_tree_644_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; lean_object* v_unused_688_; lean_object* v_unused_689_; lean_object* v_unused_690_; lean_object* v_unused_691_; 
v_unused_687_ = lean_ctor_get(v_tree_644_, 4);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_tree_644_, 3);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_tree_644_, 2);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_tree_644_, 1);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_tree_644_, 0);
lean_dec(v_unused_691_);
v___x_681_ = v_tree_644_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_dec(v_tree_644_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 4, v___x_679_);
lean_ctor_set(v___x_681_, 3, v___y_674_);
lean_ctor_set(v___x_681_, 2, v_v_662_);
lean_ctor_set(v___x_681_, 1, v_k_661_);
lean_ctor_set(v___x_681_, 0, v___x_672_);
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_k_661_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_v_662_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v___y_674_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v___x_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_nat_add(v___x_693_, v___y_695_);
lean_dec(v___y_695_);
lean_dec(v___x_693_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_l_663_);
lean_ctor_set(v___x_641_, 3, v_l_490_);
lean_ctor_set(v___x_641_, 2, v_v_489_);
lean_ctor_set(v___x_641_, 1, v_k_488_);
lean_ctor_set(v___x_641_, 0, v___x_696_);
v___x_698_ = v___x_641_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_k_488_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_v_489_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_l_663_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = lean_nat_add(v___x_497_, v_size_647_);
if (lean_obj_tag(v_r_664_) == 0)
{
lean_object* v_size_700_; 
v_size_700_ = lean_ctor_get(v_r_664_, 0);
lean_inc(v_size_700_);
v___y_674_ = v___x_698_;
v___y_675_ = v___x_699_;
v___y_676_ = v_size_700_;
goto v___jp_673_;
}
else
{
lean_object* v___x_701_; 
v___x_701_ = lean_unsigned_to_nat(0u);
v___y_674_ = v___x_698_;
v___y_675_ = v___x_699_;
v___y_676_ = v___x_701_;
goto v___jp_673_;
}
}
}
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_711_ = lean_nat_add(v___x_497_, v_size_487_);
lean_dec(v_size_487_);
v___x_712_ = lean_nat_add(v___x_711_, v_size_647_);
lean_dec(v___x_711_);
v___x_713_ = lean_nat_add(v___x_497_, v_size_647_);
v___x_714_ = lean_nat_add(v___x_713_, v_size_660_);
lean_dec(v___x_713_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_tree_644_);
lean_ctor_set(v___x_641_, 3, v_r_491_);
lean_ctor_set(v___x_641_, 2, v_v_646_);
lean_ctor_set(v___x_641_, 1, v_k_645_);
lean_ctor_set(v___x_641_, 0, v___x_714_);
v___x_716_ = v___x_641_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_r_491_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_tree_644_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v___x_716_);
lean_ctor_set(v___x_657_, 0, v___x_712_);
v___x_718_ = v___x_657_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_k_488_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_v_489_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_490_) == 0)
{
lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_750_; 
lean_inc_ref(v_l_490_);
lean_inc(v_v_489_);
lean_inc(v_k_488_);
lean_inc(v_size_487_);
v_isSharedCheck_750_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; lean_object* v_unused_754_; lean_object* v_unused_755_; 
v_unused_751_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_l_307_, 2);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_l_307_, 1);
lean_dec(v_unused_754_);
v_unused_755_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_755_);
v___x_728_ = v_l_307_;
v_isShared_729_ = v_isSharedCheck_750_;
goto v_resetjp_727_;
}
else
{
lean_dec(v_l_307_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_750_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
if (lean_obj_tag(v_r_491_) == 0)
{
lean_object* v_k_730_; lean_object* v_v_731_; lean_object* v_size_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v_k_730_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_730_);
v_v_731_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_731_);
lean_dec_ref(v___x_643_);
v_size_732_ = lean_ctor_get(v_r_491_, 0);
v___x_733_ = lean_nat_add(v___x_497_, v_size_487_);
lean_dec(v_size_487_);
v___x_734_ = lean_nat_add(v___x_497_, v_size_732_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_tree_644_);
lean_ctor_set(v___x_641_, 3, v_r_491_);
lean_ctor_set(v___x_641_, 2, v_v_731_);
lean_ctor_set(v___x_641_, 1, v_k_730_);
lean_ctor_set(v___x_641_, 0, v___x_734_);
v___x_736_ = v___x_641_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_k_730_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_v_731_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_r_491_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v_tree_644_);
v___x_736_ = v_reuseFailAlloc_740_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_738_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v___x_736_);
lean_ctor_set(v___x_728_, 0, v___x_733_);
v___x_738_ = v___x_728_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_k_488_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_v_489_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
else
{
lean_object* v_k_741_; lean_object* v_v_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
lean_dec(v_size_487_);
v_k_741_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_741_);
v_v_742_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_742_);
lean_dec_ref(v___x_643_);
v___x_743_ = lean_unsigned_to_nat(3u);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_r_491_);
lean_ctor_set(v___x_641_, 3, v_r_491_);
lean_ctor_set(v___x_641_, 2, v_v_742_);
lean_ctor_set(v___x_641_, 1, v_k_741_);
lean_ctor_set(v___x_641_, 0, v___x_497_);
v___x_745_ = v___x_641_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_k_741_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_v_742_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_r_491_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v_r_491_);
v___x_745_ = v_reuseFailAlloc_749_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_747_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v___x_745_);
lean_ctor_set(v___x_728_, 0, v___x_743_);
v___x_747_ = v___x_728_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_k_488_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_v_489_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_491_) == 0)
{
lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_780_; 
lean_inc(v_l_490_);
lean_inc(v_v_489_);
lean_inc(v_k_488_);
v_isSharedCheck_780_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; lean_object* v_unused_782_; lean_object* v_unused_783_; lean_object* v_unused_784_; lean_object* v_unused_785_; 
v_unused_781_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_l_307_, 2);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_l_307_, 1);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_785_);
v___x_757_ = v_l_307_;
v_isShared_758_ = v_isSharedCheck_780_;
goto v_resetjp_756_;
}
else
{
lean_dec(v_l_307_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_780_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_k_759_; lean_object* v_v_760_; lean_object* v_k_761_; lean_object* v_v_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_776_; 
v_k_759_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_759_);
v_v_760_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_760_);
lean_dec_ref(v___x_643_);
v_k_761_ = lean_ctor_get(v_r_491_, 1);
v_v_762_ = lean_ctor_get(v_r_491_, 2);
v_isSharedCheck_776_ = !lean_is_exclusive(v_r_491_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; lean_object* v_unused_778_; lean_object* v_unused_779_; 
v_unused_777_ = lean_ctor_get(v_r_491_, 4);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_r_491_, 3);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_r_491_, 0);
lean_dec(v_unused_779_);
v___x_764_ = v_r_491_;
v_isShared_765_ = v_isSharedCheck_776_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_v_762_);
lean_inc(v_k_761_);
lean_dec(v_r_491_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_776_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(3u);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 4, v_l_490_);
lean_ctor_set(v___x_764_, 3, v_l_490_);
lean_ctor_set(v___x_764_, 2, v_v_489_);
lean_ctor_set(v___x_764_, 1, v_k_488_);
lean_ctor_set(v___x_764_, 0, v___x_497_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_k_488_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_v_489_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_l_490_);
v___x_768_ = v_reuseFailAlloc_775_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_l_490_);
lean_ctor_set(v___x_641_, 3, v_l_490_);
lean_ctor_set(v___x_641_, 2, v_v_760_);
lean_ctor_set(v___x_641_, 1, v_k_759_);
lean_ctor_set(v___x_641_, 0, v___x_497_);
v___x_770_ = v___x_641_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_k_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_v_760_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_l_490_);
v___x_770_ = v_reuseFailAlloc_774_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_772_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 4, v___x_770_);
lean_ctor_set(v___x_757_, 3, v___x_768_);
lean_ctor_set(v___x_757_, 2, v_v_762_);
lean_ctor_set(v___x_757_, 1, v_k_761_);
lean_ctor_set(v___x_757_, 0, v___x_766_);
v___x_772_ = v___x_757_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_k_761_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_v_762_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
else
{
lean_object* v_k_786_; lean_object* v_v_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v_k_786_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_786_);
v_v_787_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_787_);
lean_dec_ref(v___x_643_);
v___x_788_ = lean_unsigned_to_nat(2u);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_r_491_);
lean_ctor_set(v___x_641_, 3, v_l_307_);
lean_ctor_set(v___x_641_, 2, v_v_787_);
lean_ctor_set(v___x_641_, 1, v_k_786_);
lean_ctor_set(v___x_641_, 0, v___x_788_);
v___x_790_ = v___x_641_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_k_786_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_v_787_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_r_491_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
}
}
else
{
return v_l_307_;
}
}
else
{
return v_r_308_;
}
}
default: 
{
lean_object* v_impl_798_; lean_object* v___x_799_; 
v_impl_798_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_303_, v_r_308_);
v___x_799_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_798_) == 0)
{
if (lean_obj_tag(v_l_307_) == 0)
{
lean_object* v_size_800_; lean_object* v_size_801_; lean_object* v_k_802_; lean_object* v_v_803_; lean_object* v_l_804_; lean_object* v_r_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_size_800_ = lean_ctor_get(v_impl_798_, 0);
lean_inc(v_size_800_);
v_size_801_ = lean_ctor_get(v_l_307_, 0);
v_k_802_ = lean_ctor_get(v_l_307_, 1);
v_v_803_ = lean_ctor_get(v_l_307_, 2);
v_l_804_ = lean_ctor_get(v_l_307_, 3);
v_r_805_ = lean_ctor_get(v_l_307_, 4);
lean_inc(v_r_805_);
v___x_806_ = lean_unsigned_to_nat(3u);
v___x_807_ = lean_nat_mul(v___x_806_, v_size_800_);
v___x_808_ = lean_nat_dec_lt(v___x_807_, v_size_801_);
lean_dec(v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
lean_dec(v_r_805_);
v___x_809_ = lean_nat_add(v___x_799_, v_size_801_);
v___x_810_ = lean_nat_add(v___x_809_, v_size_800_);
lean_dec(v_size_800_);
lean_dec(v___x_809_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_impl_798_);
lean_ctor_set(v___x_310_, 0, v___x_810_);
v___x_812_ = v___x_310_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_impl_798_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
else
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_879_; 
lean_inc(v_l_804_);
lean_inc(v_v_803_);
lean_inc(v_k_802_);
lean_inc(v_size_801_);
v_isSharedCheck_879_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; lean_object* v_unused_881_; lean_object* v_unused_882_; lean_object* v_unused_883_; lean_object* v_unused_884_; 
v_unused_880_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_880_);
v_unused_881_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v_l_307_, 2);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_l_307_, 1);
lean_dec(v_unused_883_);
v_unused_884_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_884_);
v___x_815_ = v_l_307_;
v_isShared_816_ = v_isSharedCheck_879_;
goto v_resetjp_814_;
}
else
{
lean_dec(v_l_307_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_879_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_size_817_; lean_object* v_size_818_; lean_object* v_k_819_; lean_object* v_v_820_; lean_object* v_l_821_; lean_object* v_r_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_size_817_ = lean_ctor_get(v_l_804_, 0);
v_size_818_ = lean_ctor_get(v_r_805_, 0);
v_k_819_ = lean_ctor_get(v_r_805_, 1);
v_v_820_ = lean_ctor_get(v_r_805_, 2);
v_l_821_ = lean_ctor_get(v_r_805_, 3);
v_r_822_ = lean_ctor_get(v_r_805_, 4);
v___x_823_ = lean_unsigned_to_nat(2u);
v___x_824_ = lean_nat_mul(v___x_823_, v_size_817_);
v___x_825_ = lean_nat_dec_lt(v_size_818_, v___x_824_);
lean_dec(v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_854_; 
lean_inc(v_r_822_);
lean_inc(v_l_821_);
lean_inc(v_v_820_);
lean_inc(v_k_819_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_r_805_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; 
v_unused_855_ = lean_ctor_get(v_r_805_, 4);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_r_805_, 3);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_r_805_, 2);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_r_805_, 1);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_r_805_, 0);
lean_dec(v_unused_859_);
v___x_827_ = v_r_805_;
v_isShared_828_ = v_isSharedCheck_854_;
goto v_resetjp_826_;
}
else
{
lean_dec(v_r_805_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_854_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___x_842_; lean_object* v___y_844_; 
v___x_829_ = lean_nat_add(v___x_799_, v_size_801_);
lean_dec(v_size_801_);
v___x_830_ = lean_nat_add(v___x_829_, v_size_800_);
lean_dec(v___x_829_);
v___x_842_ = lean_nat_add(v___x_799_, v_size_817_);
if (lean_obj_tag(v_l_821_) == 0)
{
lean_object* v_size_852_; 
v_size_852_ = lean_ctor_get(v_l_821_, 0);
lean_inc(v_size_852_);
v___y_844_ = v_size_852_;
goto v___jp_843_;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v___y_844_ = v___x_853_;
goto v___jp_843_;
}
v___jp_831_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = lean_nat_add(v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec(v___y_833_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 4, v_impl_798_);
lean_ctor_set(v___x_827_, 3, v_r_822_);
lean_ctor_set(v___x_827_, 2, v_v_306_);
lean_ctor_set(v___x_827_, 1, v_k_305_);
lean_ctor_set(v___x_827_, 0, v___x_835_);
v___x_837_ = v___x_827_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v_r_822_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v_impl_798_);
v___x_837_ = v_reuseFailAlloc_841_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_839_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 4, v___x_837_);
lean_ctor_set(v___x_815_, 3, v___y_832_);
lean_ctor_set(v___x_815_, 2, v_v_820_);
lean_ctor_set(v___x_815_, 1, v_k_819_);
lean_ctor_set(v___x_815_, 0, v___x_830_);
v___x_839_ = v___x_815_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v___y_832_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
v___jp_843_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_nat_add(v___x_842_, v___y_844_);
lean_dec(v___y_844_);
lean_dec(v___x_842_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_l_821_);
lean_ctor_set(v___x_310_, 3, v_l_804_);
lean_ctor_set(v___x_310_, 2, v_v_803_);
lean_ctor_set(v___x_310_, 1, v_k_802_);
lean_ctor_set(v___x_310_, 0, v___x_845_);
v___x_847_ = v___x_310_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_l_804_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v_l_821_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
v___x_848_ = lean_nat_add(v___x_799_, v_size_800_);
lean_dec(v_size_800_);
if (lean_obj_tag(v_r_822_) == 0)
{
lean_object* v_size_849_; 
v_size_849_ = lean_ctor_get(v_r_822_, 0);
lean_inc(v_size_849_);
v___y_832_ = v___x_847_;
v___y_833_ = v___x_848_;
v___y_834_ = v_size_849_;
goto v___jp_831_;
}
else
{
lean_object* v___x_850_; 
v___x_850_ = lean_unsigned_to_nat(0u);
v___y_832_ = v___x_847_;
v___y_833_ = v___x_848_;
v___y_834_ = v___x_850_;
goto v___jp_831_;
}
}
}
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
lean_del_object(v___x_310_);
v___x_860_ = lean_nat_add(v___x_799_, v_size_801_);
lean_dec(v_size_801_);
v___x_861_ = lean_nat_add(v___x_860_, v_size_800_);
lean_dec(v___x_860_);
v___x_862_ = lean_nat_add(v___x_799_, v_size_800_);
lean_dec(v_size_800_);
v___x_863_ = lean_nat_add(v___x_862_, v_size_818_);
lean_dec(v___x_862_);
lean_inc_ref(v_impl_798_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 4, v_impl_798_);
lean_ctor_set(v___x_815_, 3, v_r_805_);
lean_ctor_set(v___x_815_, 2, v_v_306_);
lean_ctor_set(v___x_815_, 1, v_k_305_);
lean_ctor_set(v___x_815_, 0, v___x_863_);
v___x_865_ = v___x_815_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v_r_805_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v_impl_798_);
v___x_865_ = v_reuseFailAlloc_878_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_isSharedCheck_872_ = !lean_is_exclusive(v_impl_798_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; lean_object* v_unused_874_; lean_object* v_unused_875_; lean_object* v_unused_876_; lean_object* v_unused_877_; 
v_unused_873_ = lean_ctor_get(v_impl_798_, 4);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_impl_798_, 3);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_impl_798_, 2);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_impl_798_, 1);
lean_dec(v_unused_876_);
v_unused_877_ = lean_ctor_get(v_impl_798_, 0);
lean_dec(v_unused_877_);
v___x_867_ = v_impl_798_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_dec(v_impl_798_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v___x_865_);
lean_ctor_set(v___x_867_, 3, v_l_804_);
lean_ctor_set(v___x_867_, 2, v_v_803_);
lean_ctor_set(v___x_867_, 1, v_k_802_);
lean_ctor_set(v___x_867_, 0, v___x_861_);
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_871_, 3, v_l_804_);
lean_ctor_set(v_reuseFailAlloc_871_, 4, v___x_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v_size_885_ = lean_ctor_get(v_impl_798_, 0);
lean_inc(v_size_885_);
v___x_886_ = lean_nat_add(v___x_799_, v_size_885_);
lean_dec(v_size_885_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_impl_798_);
lean_ctor_set(v___x_310_, 0, v___x_886_);
v___x_888_ = v___x_310_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_impl_798_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
if (lean_obj_tag(v_l_307_) == 0)
{
lean_object* v_l_890_; 
v_l_890_ = lean_ctor_get(v_l_307_, 3);
if (lean_obj_tag(v_l_890_) == 0)
{
lean_object* v_r_891_; 
lean_inc_ref(v_l_890_);
v_r_891_ = lean_ctor_get(v_l_307_, 4);
lean_inc(v_r_891_);
if (lean_obj_tag(v_r_891_) == 0)
{
lean_object* v_size_892_; lean_object* v_k_893_; lean_object* v_v_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_907_; 
v_size_892_ = lean_ctor_get(v_l_307_, 0);
v_k_893_ = lean_ctor_get(v_l_307_, 1);
v_v_894_ = lean_ctor_get(v_l_307_, 2);
v_isSharedCheck_907_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; 
v_unused_908_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_909_);
v___x_896_ = v_l_307_;
v_isShared_897_ = v_isSharedCheck_907_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_v_894_);
lean_inc(v_k_893_);
lean_inc(v_size_892_);
lean_dec(v_l_307_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_907_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_size_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v_size_898_ = lean_ctor_get(v_r_891_, 0);
v___x_899_ = lean_nat_add(v___x_799_, v_size_892_);
lean_dec(v_size_892_);
v___x_900_ = lean_nat_add(v___x_799_, v_size_898_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 4, v_impl_798_);
lean_ctor_set(v___x_896_, 3, v_r_891_);
lean_ctor_set(v___x_896_, 2, v_v_306_);
lean_ctor_set(v___x_896_, 1, v_k_305_);
lean_ctor_set(v___x_896_, 0, v___x_900_);
v___x_902_ = v___x_896_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_r_891_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_impl_798_);
v___x_902_ = v_reuseFailAlloc_906_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v___x_902_);
lean_ctor_set(v___x_310_, 3, v_l_890_);
lean_ctor_set(v___x_310_, 2, v_v_894_);
lean_ctor_set(v___x_310_, 1, v_k_893_);
lean_ctor_set(v___x_310_, 0, v___x_899_);
v___x_904_ = v___x_310_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_893_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_894_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_l_890_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_k_910_; lean_object* v_v_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_922_; 
v_k_910_ = lean_ctor_get(v_l_307_, 1);
v_v_911_ = lean_ctor_get(v_l_307_, 2);
v_isSharedCheck_922_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; lean_object* v_unused_924_; lean_object* v_unused_925_; 
v_unused_923_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_924_);
v_unused_925_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_925_);
v___x_913_ = v_l_307_;
v_isShared_914_ = v_isSharedCheck_922_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_v_911_);
lean_inc(v_k_910_);
lean_dec(v_l_307_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_922_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_unsigned_to_nat(3u);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 3, v_r_891_);
lean_ctor_set(v___x_913_, 2, v_v_306_);
lean_ctor_set(v___x_913_, 1, v_k_305_);
lean_ctor_set(v___x_913_, 0, v___x_799_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_r_891_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_r_891_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v___x_917_);
lean_ctor_set(v___x_310_, 3, v_l_890_);
lean_ctor_set(v___x_310_, 2, v_v_911_);
lean_ctor_set(v___x_310_, 1, v_k_910_);
lean_ctor_set(v___x_310_, 0, v___x_915_);
v___x_919_ = v___x_310_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_k_910_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_v_911_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_l_890_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
else
{
lean_object* v_r_926_; 
v_r_926_ = lean_ctor_get(v_l_307_, 4);
lean_inc(v_r_926_);
if (lean_obj_tag(v_r_926_) == 0)
{
lean_object* v_k_927_; lean_object* v_v_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_951_; 
lean_inc(v_l_890_);
v_k_927_ = lean_ctor_get(v_l_307_, 1);
v_v_928_ = lean_ctor_get(v_l_307_, 2);
v_isSharedCheck_951_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; 
v_unused_952_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_954_);
v___x_930_ = v_l_307_;
v_isShared_931_ = v_isSharedCheck_951_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_v_928_);
lean_inc(v_k_927_);
lean_dec(v_l_307_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_951_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_k_932_; lean_object* v_v_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_947_; 
v_k_932_ = lean_ctor_get(v_r_926_, 1);
v_v_933_ = lean_ctor_get(v_r_926_, 2);
v_isSharedCheck_947_ = !lean_is_exclusive(v_r_926_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; lean_object* v_unused_949_; lean_object* v_unused_950_; 
v_unused_948_ = lean_ctor_get(v_r_926_, 4);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_r_926_, 3);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v_r_926_, 0);
lean_dec(v_unused_950_);
v___x_935_ = v_r_926_;
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_v_933_);
lean_inc(v_k_932_);
lean_dec(v_r_926_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = lean_unsigned_to_nat(3u);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 4, v_l_890_);
lean_ctor_set(v___x_935_, 3, v_l_890_);
lean_ctor_set(v___x_935_, 2, v_v_928_);
lean_ctor_set(v___x_935_, 1, v_k_927_);
lean_ctor_set(v___x_935_, 0, v___x_799_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_k_927_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_v_928_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_l_890_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_l_890_);
v___x_939_ = v_reuseFailAlloc_946_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v_l_890_);
lean_ctor_set(v___x_930_, 2, v_v_306_);
lean_ctor_set(v___x_930_, 1, v_k_305_);
lean_ctor_set(v___x_930_, 0, v___x_799_);
v___x_941_ = v___x_930_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_l_890_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_l_890_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v___x_941_);
lean_ctor_set(v___x_310_, 3, v___x_939_);
lean_ctor_set(v___x_310_, 2, v_v_933_);
lean_ctor_set(v___x_310_, 1, v_k_932_);
lean_ctor_set(v___x_310_, 0, v___x_937_);
v___x_943_ = v___x_310_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v___x_941_);
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
}
}
else
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = lean_unsigned_to_nat(2u);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_r_926_);
lean_ctor_set(v___x_310_, 0, v___x_955_);
v___x_957_ = v___x_310_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_r_926_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_object* v___x_960_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_l_307_);
lean_ctor_set(v___x_310_, 0, v___x_799_);
v___x_960_ = v___x_310_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_961_, 4, v_l_307_);
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
}
}
}
else
{
return v_t_304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg___boxed(lean_object* v_k_964_, lean_object* v_t_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_964_, v_t_965_);
lean_dec(v_k_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString(lean_object* v_declName_967_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_969_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_970_ = lean_st_ref_take(v___x_969_);
v___x_971_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_declName_967_, v___x_970_);
v___x_972_ = lean_st_ref_set(v___x_969_, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString___boxed(lean_object* v_declName_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_removeBuiltinDocString(v_declName_974_);
lean_dec(v_declName_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(lean_object* v_00_u03b2_977_, lean_object* v_k_978_, lean_object* v_t_979_, lean_object* v_h_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_978_, v_t_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___boxed(lean_object* v_00_u03b2_982_, lean_object* v_k_983_, lean_object* v_t_984_, lean_object* v_h_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(v_00_u03b2_982_, v_k_983_, v_t_984_, v_h_985_);
lean_dec(v_k_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings(){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_989_ = lean_st_ref_get(v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings___boxed(lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_getBuiltinVersoDocStrings();
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object* v_docString_993_, lean_object* v_declName_994_, lean_object* v_env_995_){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = l_Lean_docStringExt;
v___x_997_ = l_String_removeLeadingSpaces(v_docString_993_);
v___x_998_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_996_, v_env_995_, v_declName_994_, v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_999_, lean_object* v___f_1000_, lean_object* v_____r_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_apply_1(v_modifyEnv_999_, v___f_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__0));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__2));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object* v_declName_1009_, lean_object* v_modifyEnv_1010_, lean_object* v___f_1011_, lean_object* v_inst_1012_, lean_object* v_inst_1013_, lean_object* v_toBind_1014_, lean_object* v___f_1015_, lean_object* v_____do__lift_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1016_, v_declName_1009_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v___x_1018_; 
lean_dec(v___f_1015_);
lean_dec(v_toBind_1014_);
lean_dec_ref(v_inst_1013_);
lean_dec_ref(v_inst_1012_);
lean_dec(v_declName_1009_);
v___x_1018_ = lean_apply_1(v_modifyEnv_1010_, v___f_1011_);
return v___x_1018_;
}
else
{
uint8_t v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_dec_ref_known(v___x_1017_, 1);
lean_dec_ref(v___f_1011_);
lean_dec(v_modifyEnv_1010_);
v___x_1019_ = 0;
v___x_1020_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1021_ = l_Lean_MessageData_ofConstName(v_declName_1009_, v___x_1019_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = l_Lean_throwError___redArg(v_inst_1012_, v_inst_1013_, v___x_1024_);
v___x_1026_ = lean_apply_4(v_toBind_1014_, lean_box(0), lean_box(0), v___x_1025_, v___f_1015_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1027_, lean_object* v_modifyEnv_1028_, lean_object* v___f_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_toBind_1032_, lean_object* v___f_1033_, lean_object* v_____do__lift_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_addDocStringCore___redArg___lam__2(v_declName_1027_, v_modifyEnv_1028_, v___f_1029_, v_inst_1030_, v_inst_1031_, v_toBind_1032_, v___f_1033_, v_____do__lift_1034_);
lean_dec_ref(v_____do__lift_1034_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_declName_1039_, lean_object* v_docString_1040_){
_start:
{
lean_object* v_toBind_1041_; lean_object* v_getEnv_1042_; lean_object* v_modifyEnv_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___x_1047_; 
v_toBind_1041_ = lean_ctor_get(v_inst_1036_, 1);
lean_inc_n(v_toBind_1041_, 2);
v_getEnv_1042_ = lean_ctor_get(v_inst_1038_, 0);
lean_inc(v_getEnv_1042_);
v_modifyEnv_1043_ = lean_ctor_get(v_inst_1038_, 1);
lean_inc_n(v_modifyEnv_1043_, 2);
lean_dec_ref(v_inst_1038_);
lean_inc(v_declName_1039_);
v___f_1044_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1044_, 0, v_docString_1040_);
lean_closure_set(v___f_1044_, 1, v_declName_1039_);
lean_inc_ref(v___f_1044_);
v___f_1045_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1045_, 0, v_modifyEnv_1043_);
lean_closure_set(v___f_1045_, 1, v___f_1044_);
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1046_, 0, v_declName_1039_);
lean_closure_set(v___f_1046_, 1, v_modifyEnv_1043_);
lean_closure_set(v___f_1046_, 2, v___f_1044_);
lean_closure_set(v___f_1046_, 3, v_inst_1036_);
lean_closure_set(v___f_1046_, 4, v_inst_1037_);
lean_closure_set(v___f_1046_, 5, v_toBind_1041_);
lean_closure_set(v___f_1046_, 6, v___f_1045_);
v___x_1047_ = lean_apply_4(v_toBind_1041_, lean_box(0), lean_box(0), v_getEnv_1042_, v___f_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object* v_m_1048_, lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_declName_1053_, lean_object* v_docString_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_addDocStringCore___redArg(v_inst_1049_, v_inst_1050_, v_inst_1051_, v_declName_1053_, v_docString_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object* v_m_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_declName_1061_, lean_object* v_docString_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_addDocStringCore(v_m_1056_, v_inst_1057_, v_inst_1058_, v_inst_1059_, v_inst_1060_, v_declName_1061_, v_docString_1062_);
lean_dec(v_inst_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object* v_declName_1065_, lean_object* v_x_1066_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__0___closed__0));
v___x_1068_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_1067_, v_declName_1065_, v_x_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object* v___f_1069_, lean_object* v_env_1070_){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1071_ = l_Lean_docStringExt;
v___x_1072_ = lean_box(2);
v___x_1073_ = lean_box(0);
v___x_1074_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_1071_, v_env_1070_, v___f_1069_, v___x_1072_, v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__3___closed__0));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object* v_declName_1078_, lean_object* v_modifyEnv_1079_, lean_object* v___f_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_toBind_1083_, lean_object* v___f_1084_, lean_object* v_____do__lift_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1085_, v_declName_1078_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v___x_1087_; 
lean_dec(v___f_1084_);
lean_dec(v_toBind_1083_);
lean_dec_ref(v_inst_1082_);
lean_dec_ref(v_inst_1081_);
lean_dec(v_declName_1078_);
v___x_1087_ = lean_apply_1(v_modifyEnv_1079_, v___f_1080_);
return v___x_1087_;
}
else
{
uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec_ref_known(v___x_1086_, 1);
lean_dec_ref(v___f_1080_);
lean_dec(v_modifyEnv_1079_);
v___x_1088_ = 0;
v___x_1089_ = lean_obj_once(&l_Lean_removeDocStringCore___redArg___lam__3___closed__1, &l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1);
v___x_1090_ = l_Lean_MessageData_ofConstName(v_declName_1078_, v___x_1088_);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_throwError___redArg(v_inst_1081_, v_inst_1082_, v___x_1093_);
v___x_1095_ = lean_apply_4(v_toBind_1083_, lean_box(0), lean_box(0), v___x_1094_, v___f_1084_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1096_, lean_object* v_modifyEnv_1097_, lean_object* v___f_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_toBind_1101_, lean_object* v___f_1102_, lean_object* v_____do__lift_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_removeDocStringCore___redArg___lam__3(v_declName_1096_, v_modifyEnv_1097_, v___f_1098_, v_inst_1099_, v_inst_1100_, v_toBind_1101_, v___f_1102_, v_____do__lift_1103_);
lean_dec_ref(v_____do__lift_1103_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_declName_1108_){
_start:
{
lean_object* v_toBind_1109_; lean_object* v_getEnv_1110_; lean_object* v_modifyEnv_1111_; lean_object* v___f_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___f_1115_; lean_object* v___x_1116_; 
v_toBind_1109_ = lean_ctor_get(v_inst_1105_, 1);
lean_inc_n(v_toBind_1109_, 2);
v_getEnv_1110_ = lean_ctor_get(v_inst_1107_, 0);
lean_inc(v_getEnv_1110_);
v_modifyEnv_1111_ = lean_ctor_get(v_inst_1107_, 1);
lean_inc_n(v_modifyEnv_1111_, 2);
lean_dec_ref(v_inst_1107_);
lean_inc(v_declName_1108_);
v___f_1112_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1112_, 0, v_declName_1108_);
v___f_1113_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1113_, 0, v___f_1112_);
lean_inc_ref(v___f_1113_);
v___f_1114_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1114_, 0, v_modifyEnv_1111_);
lean_closure_set(v___f_1114_, 1, v___f_1113_);
v___f_1115_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1115_, 0, v_declName_1108_);
lean_closure_set(v___f_1115_, 1, v_modifyEnv_1111_);
lean_closure_set(v___f_1115_, 2, v___f_1113_);
lean_closure_set(v___f_1115_, 3, v_inst_1105_);
lean_closure_set(v___f_1115_, 4, v_inst_1106_);
lean_closure_set(v___f_1115_, 5, v_toBind_1109_);
lean_closure_set(v___f_1115_, 6, v___f_1114_);
v___x_1116_ = lean_apply_4(v_toBind_1109_, lean_box(0), lean_box(0), v_getEnv_1110_, v___f_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object* v_m_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_declName_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_removeDocStringCore___redArg(v_inst_1118_, v_inst_1119_, v_inst_1120_, v_declName_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object* v_m_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_declName_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_removeDocStringCore(v_m_1124_, v_inst_1125_, v_inst_1126_, v_inst_1127_, v_inst_1128_, v_declName_1129_);
lean_dec(v_inst_1128_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_declName_1134_, lean_object* v_docString_x3f_1135_){
_start:
{
if (lean_obj_tag(v_docString_x3f_1135_) == 0)
{
lean_object* v_toApplicative_1136_; lean_object* v_toPure_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_toApplicative_1136_ = lean_ctor_get(v_inst_1131_, 0);
lean_inc_ref(v_toApplicative_1136_);
lean_dec(v_declName_1134_);
lean_dec_ref(v_inst_1133_);
lean_dec_ref(v_inst_1132_);
lean_dec_ref(v_inst_1131_);
v_toPure_1137_ = lean_ctor_get(v_toApplicative_1136_, 1);
lean_inc(v_toPure_1137_);
lean_dec_ref(v_toApplicative_1136_);
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_apply_2(v_toPure_1137_, lean_box(0), v___x_1138_);
return v___x_1139_;
}
else
{
lean_object* v_val_1140_; lean_object* v___x_1141_; 
v_val_1140_ = lean_ctor_get(v_docString_x3f_1135_, 0);
lean_inc(v_val_1140_);
lean_dec_ref_known(v_docString_x3f_1135_, 1);
v___x_1141_ = l_Lean_addDocStringCore___redArg(v_inst_1131_, v_inst_1132_, v_inst_1133_, v_declName_1134_, v_val_1140_);
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object* v_m_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_declName_1147_, lean_object* v_docString_x3f_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_addDocStringCore_x27___redArg(v_inst_1143_, v_inst_1144_, v_inst_1145_, v_declName_1147_, v_docString_x3f_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object* v_m_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_declName_1155_, lean_object* v_docString_x3f_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_addDocStringCore_x27(v_m_1150_, v_inst_1151_, v_inst_1152_, v_inst_1153_, v_inst_1154_, v_declName_1155_, v_docString_x3f_1156_);
lean_dec(v_inst_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object* v_declName_1158_, lean_object* v_target_1159_, lean_object* v_env_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1162_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1161_, v_env_1160_, v_declName_1158_, v_target_1159_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__2___closed__0));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object* v___x_1166_, lean_object* v_target_1167_, lean_object* v_declName_1168_, lean_object* v___x_1169_, lean_object* v_modifyEnv_1170_, lean_object* v___f_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_toBind_1174_, lean_object* v___f_1175_, lean_object* v_____do__lift_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v_toEnvExtension_1178_; lean_object* v_asyncMode_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1177_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1178_ = lean_ctor_get(v___x_1177_, 0);
v_asyncMode_1179_ = lean_ctor_get(v_toEnvExtension_1178_, 2);
v___x_1180_ = 1;
v___x_1181_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1166_, v___x_1177_, v_____do__lift_1176_, v_target_1167_, v_asyncMode_1179_, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_declName_1168_);
v___x_1183_ = l_Option_instBEq_beq___redArg(v___x_1169_, v___x_1181_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
lean_dec(v___f_1175_);
lean_dec(v_toBind_1174_);
lean_dec_ref(v_inst_1173_);
lean_dec_ref(v_inst_1172_);
v___x_1184_ = lean_apply_1(v_modifyEnv_1170_, v___f_1171_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec_ref(v___f_1171_);
lean_dec(v_modifyEnv_1170_);
v___x_1185_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__2___closed__1, &l_Lean_addInheritedDocString___redArg___lam__2___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1);
v___x_1186_ = l_Lean_throwError___redArg(v_inst_1172_, v_inst_1173_, v___x_1185_);
v___x_1187_ = lean_apply_4(v_toBind_1174_, lean_box(0), lean_box(0), v___x_1186_, v___f_1175_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object* v_toBind_1188_, lean_object* v_getEnv_1189_, lean_object* v___f_1190_, lean_object* v_____r_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_apply_4(v_toBind_1188_, lean_box(0), lean_box(0), v_getEnv_1189_, v___f_1190_);
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__0));
v___x_1195_ = l_Lean_stringToMessageData(v___x_1194_);
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__2));
v___x_1198_ = l_Lean_stringToMessageData(v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object* v___x_1199_, lean_object* v_declName_1200_, lean_object* v_toBind_1201_, lean_object* v_getEnv_1202_, lean_object* v___f_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v___f_1206_, lean_object* v_____do__lift_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v_toEnvExtension_1209_; lean_object* v_asyncMode_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; 
v___x_1208_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1209_ = lean_ctor_get(v___x_1208_, 0);
v_asyncMode_1210_ = lean_ctor_get(v_toEnvExtension_1209_, 2);
v___x_1211_ = 1;
lean_inc(v_declName_1200_);
v___x_1212_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1199_, v___x_1208_, v_____do__lift_1207_, v_declName_1200_, v_asyncMode_1210_, v___x_1211_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v___x_1213_; 
lean_dec(v___f_1206_);
lean_dec_ref(v_inst_1205_);
lean_dec_ref(v_inst_1204_);
lean_dec(v_declName_1200_);
v___x_1213_ = lean_apply_4(v_toBind_1201_, lean_box(0), lean_box(0), v_getEnv_1202_, v___f_1203_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; uint8_t v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref_known(v___x_1212_, 1);
lean_dec(v___f_1203_);
lean_dec(v_getEnv_1202_);
v___x_1214_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1215_ = 0;
v___x_1216_ = l_Lean_MessageData_ofConstName(v_declName_1200_, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1214_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__3, &l_Lean_addInheritedDocString___redArg___lam__3___closed__3_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3);
v___x_1219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = l_Lean_throwError___redArg(v_inst_1204_, v_inst_1205_, v___x_1219_);
v___x_1221_ = lean_apply_4(v_toBind_1201_, lean_box(0), lean_box(0), v___x_1220_, v___f_1206_);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object* v_declName_1222_, lean_object* v_toBind_1223_, lean_object* v_getEnv_1224_, lean_object* v___f_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v___f_1228_, lean_object* v_____do__lift_1229_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1229_, v_declName_1222_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v___x_1231_; 
lean_dec(v___f_1228_);
lean_dec_ref(v_inst_1227_);
lean_dec_ref(v_inst_1226_);
lean_dec(v_declName_1222_);
v___x_1231_ = lean_apply_4(v_toBind_1223_, lean_box(0), lean_box(0), v_getEnv_1224_, v___f_1225_);
return v___x_1231_;
}
else
{
uint8_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec_ref_known(v___x_1230_, 1);
lean_dec(v___f_1225_);
lean_dec(v_getEnv_1224_);
v___x_1232_ = 0;
v___x_1233_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1234_ = l_Lean_MessageData_ofConstName(v_declName_1222_, v___x_1232_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_throwError___redArg(v_inst_1226_, v_inst_1227_, v___x_1237_);
v___x_1239_ = lean_apply_4(v_toBind_1223_, lean_box(0), lean_box(0), v___x_1238_, v___f_1228_);
return v___x_1239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object* v_declName_1240_, lean_object* v_toBind_1241_, lean_object* v_getEnv_1242_, lean_object* v___f_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v___f_1246_, lean_object* v_____do__lift_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_addInheritedDocString___redArg___lam__5(v_declName_1240_, v_toBind_1241_, v_getEnv_1242_, v___f_1243_, v_inst_1244_, v_inst_1245_, v___f_1246_, v_____do__lift_1247_);
lean_dec_ref(v_____do__lift_1247_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_declName_1253_, lean_object* v_target_1254_){
_start:
{
lean_object* v_toBind_1255_; lean_object* v_getEnv_1256_; lean_object* v_modifyEnv_1257_; lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___f_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; 
v_toBind_1255_ = lean_ctor_get(v_inst_1250_, 1);
lean_inc_n(v_toBind_1255_, 6);
v_getEnv_1256_ = lean_ctor_get(v_inst_1252_, 0);
lean_inc_n(v_getEnv_1256_, 5);
v_modifyEnv_1257_ = lean_ctor_get(v_inst_1252_, 1);
lean_inc_n(v_modifyEnv_1257_, 2);
lean_dec_ref(v_inst_1252_);
lean_inc(v_target_1254_);
lean_inc_n(v_declName_1253_, 3);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1258_, 0, v_declName_1253_);
lean_closure_set(v___f_1258_, 1, v_target_1254_);
lean_inc_ref(v___f_1258_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1259_, 0, v_modifyEnv_1257_);
lean_closure_set(v___f_1259_, 1, v___f_1258_);
v___x_1260_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___closed__0));
v___x_1261_ = lean_box(0);
lean_inc_ref_n(v_inst_1251_, 2);
lean_inc_ref_n(v_inst_1250_, 2);
v___f_1262_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__2), 11, 10);
lean_closure_set(v___f_1262_, 0, v___x_1261_);
lean_closure_set(v___f_1262_, 1, v_target_1254_);
lean_closure_set(v___f_1262_, 2, v_declName_1253_);
lean_closure_set(v___f_1262_, 3, v___x_1260_);
lean_closure_set(v___f_1262_, 4, v_modifyEnv_1257_);
lean_closure_set(v___f_1262_, 5, v___f_1258_);
lean_closure_set(v___f_1262_, 6, v_inst_1250_);
lean_closure_set(v___f_1262_, 7, v_inst_1251_);
lean_closure_set(v___f_1262_, 8, v_toBind_1255_);
lean_closure_set(v___f_1262_, 9, v___f_1259_);
lean_inc_ref(v___f_1262_);
v___f_1263_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1263_, 0, v_toBind_1255_);
lean_closure_set(v___f_1263_, 1, v_getEnv_1256_);
lean_closure_set(v___f_1263_, 2, v___f_1262_);
v___f_1264_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__3), 9, 8);
lean_closure_set(v___f_1264_, 0, v___x_1261_);
lean_closure_set(v___f_1264_, 1, v_declName_1253_);
lean_closure_set(v___f_1264_, 2, v_toBind_1255_);
lean_closure_set(v___f_1264_, 3, v_getEnv_1256_);
lean_closure_set(v___f_1264_, 4, v___f_1262_);
lean_closure_set(v___f_1264_, 5, v_inst_1250_);
lean_closure_set(v___f_1264_, 6, v_inst_1251_);
lean_closure_set(v___f_1264_, 7, v___f_1263_);
lean_inc_ref(v___f_1264_);
v___f_1265_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1265_, 0, v_toBind_1255_);
lean_closure_set(v___f_1265_, 1, v_getEnv_1256_);
lean_closure_set(v___f_1265_, 2, v___f_1264_);
v___f_1266_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1266_, 0, v_declName_1253_);
lean_closure_set(v___f_1266_, 1, v_toBind_1255_);
lean_closure_set(v___f_1266_, 2, v_getEnv_1256_);
lean_closure_set(v___f_1266_, 3, v___f_1264_);
lean_closure_set(v___f_1266_, 4, v_inst_1250_);
lean_closure_set(v___f_1266_, 5, v_inst_1251_);
lean_closure_set(v___f_1266_, 6, v___f_1265_);
v___x_1267_ = lean_apply_4(v_toBind_1255_, lean_box(0), lean_box(0), v_getEnv_1256_, v___f_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object* v_m_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_declName_1272_, lean_object* v_target_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_addInheritedDocString___redArg(v_inst_1269_, v_inst_1270_, v_inst_1271_, v_declName_1272_, v_target_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object* v_env_1276_, lean_object* v_declName_1277_, uint8_t v_includeBuiltin_1278_){
_start:
{
lean_object* v_md_1281_; lean_object* v_v_1286_; lean_object* v___x_1293_; lean_object* v_toEnvExtension_1294_; lean_object* v_asyncMode_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1293_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1294_ = lean_ctor_get(v___x_1293_, 0);
v_asyncMode_1295_ = lean_ctor_get(v_toEnvExtension_1294_, 2);
v___x_1296_ = lean_box(0);
v___x_1297_ = 1;
lean_inc(v_declName_1277_);
lean_inc_ref(v_env_1276_);
v___x_1298_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1296_, v___x_1293_, v_env_1276_, v_declName_1277_, v_asyncMode_1295_, v___x_1297_);
if (lean_obj_tag(v___x_1298_) == 1)
{
lean_object* v_val_1299_; 
lean_dec(v_declName_1277_);
v_val_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v_declName_1277_ = v_val_1299_;
goto _start;
}
else
{
lean_object* v___x_1301_; lean_object* v_toEnvExtension_1302_; lean_object* v_asyncMode_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec(v___x_1298_);
v___x_1301_ = l_Lean_docStringExt;
v_toEnvExtension_1302_ = lean_ctor_get(v___x_1301_, 0);
v_asyncMode_1303_ = lean_ctor_get(v_toEnvExtension_1302_, 2);
v___x_1304_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
lean_inc(v_declName_1277_);
lean_inc_ref(v_env_1276_);
v___x_1305_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1304_, v___x_1301_, v_env_1276_, v_declName_1277_, v_asyncMode_1303_, v___x_1297_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v___x_1306_; lean_object* v_toEnvExtension_1307_; lean_object* v_asyncMode_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1306_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1307_ = lean_ctor_get(v___x_1306_, 0);
v_asyncMode_1308_ = lean_ctor_get(v_toEnvExtension_1307_, 2);
v___x_1309_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default));
lean_inc(v_declName_1277_);
v___x_1310_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1309_, v___x_1306_, v_env_1276_, v_declName_1277_, v_asyncMode_1308_, v___x_1297_);
if (lean_obj_tag(v___x_1310_) == 0)
{
if (v_includeBuiltin_1278_ == 0)
{
lean_dec(v_declName_1277_);
goto v___jp_1290_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1312_ = lean_st_ref_get(v___x_1311_);
v___x_1313_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1312_, v_declName_1277_);
lean_dec(v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 1)
{
lean_object* v_val_1314_; 
lean_dec(v_declName_1277_);
v_val_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_val_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v_md_1281_ = v_val_1314_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec(v___x_1313_);
v___x_1315_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1316_ = lean_st_ref_get(v___x_1315_);
v___x_1317_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1316_, v_declName_1277_);
lean_dec(v_declName_1277_);
lean_dec(v___x_1316_);
if (lean_obj_tag(v___x_1317_) == 1)
{
lean_object* v_val_1318_; 
v_val_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_val_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v_v_1286_ = v_val_1318_;
goto v___jp_1285_;
}
else
{
lean_dec(v___x_1317_);
goto v___jp_1290_;
}
}
}
}
else
{
lean_object* v_val_1319_; 
lean_dec(v_declName_1277_);
v_val_1319_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_val_1319_);
lean_dec_ref_known(v___x_1310_, 1);
v_v_1286_ = v_val_1319_;
goto v___jp_1285_;
}
}
else
{
lean_object* v_val_1320_; 
lean_dec(v_declName_1277_);
lean_dec_ref(v_env_1276_);
v_val_1320_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_val_1320_);
lean_dec_ref_known(v___x_1305_, 1);
v_md_1281_ = v_val_1320_;
goto v___jp_1280_;
}
}
v___jp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_md_1281_);
v___x_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
v___jp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1287_, 0, v_v_1286_);
v___x_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
v___jp_1290_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_box(0);
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object* v_env_1321_, lean_object* v_declName_1322_, lean_object* v_includeBuiltin_1323_, lean_object* v_a_1324_){
_start:
{
uint8_t v_includeBuiltin_boxed_1325_; lean_object* v_res_1326_; 
v_includeBuiltin_boxed_1325_ = lean_unbox(v_includeBuiltin_1323_);
v_res_1326_ = l_Lean_findInternalDocString_x3f(v_env_1321_, v_declName_1322_, v_includeBuiltin_boxed_1325_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_es_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_array_mk(v_es_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v_es_1333_){
_start:
{
lean_object* v_ents_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_ents_1334_ = lean_array_mk(v_es_1333_);
v___x_1335_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
lean_inc_ref(v_ents_1334_);
v___x_1336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v_ents_1334_);
lean_ctor_set(v___x_1336_, 2, v_ents_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_x_1337_, lean_object* v_x_1338_, lean_object* v_es_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v_x_1337_, v_x_1338_, v_es_1339_);
lean_dec_ref(v_x_1338_);
lean_dec_ref(v_x_1337_);
return v_res_1340_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_unsigned_to_nat(32u);
v___x_1342_ = lean_mk_empty_array_with_capacity(v___x_1341_);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v___x_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v___x_1346_ = lean_unsigned_to_nat(32u);
v___x_1347_ = lean_mk_empty_array_with_capacity(v___x_1346_);
v___x_1348_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_);
v___x_1349_ = ((size_t)5ULL);
lean_inc(v___x_1344_);
v___x_1350_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1347_);
lean_ctor_set(v___x_1350_, 2, v___x_1344_);
lean_ctor_set(v___x_1350_, 3, v___x_1344_);
lean_ctor_set_usize(v___x_1350_, 4, v___x_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v___x_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v___x_1351_, v_x_1352_);
lean_dec_ref(v_x_1352_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
v___x_1375_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object* v_env_1378_, lean_object* v_doc_1379_){
_start:
{
lean_object* v___x_1380_; lean_object* v_toEnvExtension_1381_; lean_object* v_asyncMode_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1380_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_1381_ = lean_ctor_get(v___x_1380_, 0);
v_asyncMode_1382_ = lean_ctor_get(v_toEnvExtension_1381_, 2);
v___x_1383_ = lean_box(0);
v___x_1384_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1380_, v_env_1378_, v_doc_1379_, v_asyncMode_1382_, v___x_1383_);
return v___x_1384_;
}
}
static lean_object* _init_l_Lean_getMainModuleDoc___closed__0(void){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object* v_env_1386_){
_start:
{
lean_object* v___x_1387_; lean_object* v_toEnvExtension_1388_; lean_object* v_asyncMode_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1387_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_1388_ = lean_ctor_get(v___x_1387_, 0);
v_asyncMode_1389_ = lean_ctor_get(v_toEnvExtension_1388_, 2);
v___x_1390_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_1391_ = lean_box(0);
v___x_1392_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1390_, v___x_1387_, v_env_1386_, v_asyncMode_1389_, v___x_1391_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lean_getModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v___x_1393_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object* v_env_1396_, lean_object* v_moduleName_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_Environment_getModuleIdx_x3f(v_env_1396_, v_moduleName_1397_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_box(0);
return v___x_1399_;
}
else
{
lean_object* v_val_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1411_; 
v_val_1400_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1402_ = v___x_1398_;
v_isShared_1403_ = v_isSharedCheck_1411_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_val_1400_);
lean_dec(v___x_1398_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1411_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1404_ = lean_obj_once(&l_Lean_getModuleDoc_x3f___closed__0, &l_Lean_getModuleDoc_x3f___closed__0_once, _init_l_Lean_getModuleDoc_x3f___closed__0);
v___x_1405_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v___x_1406_ = 1;
v___x_1407_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1404_, v___x_1405_, v_env_1396_, v_val_1400_, v___x_1406_);
lean_dec(v_val_1400_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1407_);
v___x_1409_ = v___x_1402_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object* v_env_1412_, lean_object* v_moduleName_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_getModuleDoc_x3f(v_env_1412_, v_moduleName_1413_);
lean_dec(v_moduleName_1413_);
lean_dec_ref(v_env_1412_);
return v_res_1414_;
}
}
static lean_object* _init_l_Lean_getDocStringText___redArg___closed__1(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__0));
v___x_1417_ = l_Lean_stringToMessageData(v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_stx_1423_){
_start:
{
lean_object* v_toApplicative_1430_; lean_object* v_toPure_1431_; lean_object* v_val_1433_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_toApplicative_1430_ = lean_ctor_get(v_inst_1421_, 0);
v_toPure_1431_ = lean_ctor_get(v_toApplicative_1430_, 1);
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = l_Lean_Syntax_getArg(v_stx_1423_, v___x_1440_);
switch(lean_obj_tag(v___x_1441_))
{
case 2:
{
lean_object* v_val_1442_; 
lean_inc(v_toPure_1431_);
lean_dec(v_stx_1423_);
lean_dec_ref(v_inst_1422_);
lean_dec_ref(v_inst_1421_);
v_val_1442_ = lean_ctor_get(v___x_1441_, 1);
lean_inc_ref(v_val_1442_);
lean_dec_ref_known(v___x_1441_, 2);
v_val_1433_ = v_val_1442_;
goto v___jp_1432_;
}
case 1:
{
lean_object* v_kind_1443_; 
v_kind_1443_ = lean_ctor_get(v___x_1441_, 1);
lean_inc(v_kind_1443_);
if (lean_obj_tag(v_kind_1443_) == 1)
{
lean_object* v_pre_1444_; 
v_pre_1444_ = lean_ctor_get(v_kind_1443_, 0);
lean_inc(v_pre_1444_);
if (lean_obj_tag(v_pre_1444_) == 1)
{
lean_object* v_pre_1445_; 
v_pre_1445_ = lean_ctor_get(v_pre_1444_, 0);
lean_inc(v_pre_1445_);
if (lean_obj_tag(v_pre_1445_) == 1)
{
lean_object* v_pre_1446_; 
v_pre_1446_ = lean_ctor_get(v_pre_1445_, 0);
lean_inc(v_pre_1446_);
if (lean_obj_tag(v_pre_1446_) == 1)
{
lean_object* v_pre_1447_; 
v_pre_1447_ = lean_ctor_get(v_pre_1446_, 0);
if (lean_obj_tag(v_pre_1447_) == 0)
{
lean_object* v_str_1448_; lean_object* v_str_1449_; lean_object* v_str_1450_; lean_object* v_str_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v_str_1448_ = lean_ctor_get(v_kind_1443_, 1);
lean_inc_ref(v_str_1448_);
lean_dec_ref_known(v_kind_1443_, 2);
v_str_1449_ = lean_ctor_get(v_pre_1444_, 1);
lean_inc_ref(v_str_1449_);
lean_dec_ref_known(v_pre_1444_, 2);
v_str_1450_ = lean_ctor_get(v_pre_1445_, 1);
lean_inc_ref(v_str_1450_);
lean_dec_ref_known(v_pre_1445_, 2);
v_str_1451_ = lean_ctor_get(v_pre_1446_, 1);
lean_inc_ref(v_str_1451_);
lean_dec_ref_known(v_pre_1446_, 2);
v___x_1452_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_1453_ = lean_string_dec_eq(v_str_1451_, v___x_1452_);
lean_dec_ref(v_str_1451_);
if (v___x_1453_ == 0)
{
lean_dec_ref(v_str_1450_);
lean_dec_ref(v_str_1449_);
lean_dec_ref(v_str_1448_);
lean_dec_ref_known(v___x_1441_, 3);
goto v___jp_1424_;
}
else
{
lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__2));
v___x_1455_ = lean_string_dec_eq(v_str_1450_, v___x_1454_);
lean_dec_ref(v_str_1450_);
if (v___x_1455_ == 0)
{
lean_dec_ref(v_str_1449_);
lean_dec_ref(v_str_1448_);
lean_dec_ref_known(v___x_1441_, 3);
goto v___jp_1424_;
}
else
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__3));
v___x_1457_ = lean_string_dec_eq(v_str_1449_, v___x_1456_);
lean_dec_ref(v_str_1449_);
if (v___x_1457_ == 0)
{
lean_dec_ref(v_str_1448_);
lean_dec_ref_known(v___x_1441_, 3);
goto v___jp_1424_;
}
else
{
lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1458_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__4));
v___x_1459_ = lean_string_dec_eq(v_str_1448_, v___x_1458_);
lean_dec_ref(v_str_1448_);
if (v___x_1459_ == 0)
{
lean_dec_ref_known(v___x_1441_, 3);
goto v___jp_1424_;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = l_Lean_Syntax_getArg(v___x_1441_, v___x_1460_);
lean_dec_ref_known(v___x_1441_, 3);
if (lean_obj_tag(v___x_1461_) == 2)
{
lean_object* v_val_1462_; 
lean_inc(v_toPure_1431_);
lean_dec(v_stx_1423_);
lean_dec_ref(v_inst_1422_);
lean_dec_ref(v_inst_1421_);
v_val_1462_ = lean_ctor_get(v___x_1461_, 1);
lean_inc_ref(v_val_1462_);
lean_dec_ref_known(v___x_1461_, 2);
v_val_1433_ = v_val_1462_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec(v___x_1461_);
v___x_1463_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_1423_);
v___x_1464_ = l_Lean_MessageData_ofSyntax(v_stx_1423_);
v___x_1465_ = l_Lean_indentD(v___x_1464_);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1463_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = l_Lean_throwErrorAt___redArg(v_inst_1421_, v_inst_1422_, v_stx_1423_, v___x_1466_);
return v___x_1467_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1446_, 2);
lean_dec_ref_known(v_pre_1445_, 2);
lean_dec_ref_known(v_pre_1444_, 2);
lean_dec_ref_known(v_kind_1443_, 2);
lean_dec_ref_known(v___x_1441_, 3);
goto v___jp_1424_;
}
}
else
{
lean_dec_ref_known(v_pre_1445_, 2);
lean_dec(v_pre_1446_);
lean_dec_ref_known(v_pre_1444_, 2);
lean_dec_ref_known(v_kind_1443_, 2);
lean_dec_ref_known(v___x_1441_, 3);
goto v___jp_1424_;
}
}
else
{
lean_dec_ref_known(v_pre_1444_, 2);
lean_dec(v_pre_1445_);
lean_dec_ref_known(v_kind_1443_, 2);
lean_dec_ref_known(v___x_1441_, 3);
goto v___jp_1424_;
}
}
else
{
lean_dec(v_pre_1444_);
lean_dec_ref_known(v_kind_1443_, 2);
lean_dec_ref_known(v___x_1441_, 3);
goto v___jp_1424_;
}
}
else
{
lean_dec_ref_known(v___x_1441_, 3);
lean_dec(v_kind_1443_);
goto v___jp_1424_;
}
}
default: 
{
lean_dec(v___x_1441_);
goto v___jp_1424_;
}
}
v___jp_1424_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1425_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_1423_);
v___x_1426_ = l_Lean_MessageData_ofSyntax(v_stx_1423_);
v___x_1427_ = l_Lean_indentD(v___x_1426_);
v___x_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1425_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = l_Lean_throwErrorAt___redArg(v_inst_1421_, v_inst_1422_, v_stx_1423_, v___x_1428_);
return v___x_1429_;
}
v___jp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_string_utf8_byte_size(v_val_1433_);
v___x_1436_ = lean_unsigned_to_nat(2u);
v___x_1437_ = lean_nat_sub(v___x_1435_, v___x_1436_);
v___x_1438_ = lean_string_utf8_extract(v_val_1433_, v___x_1434_, v___x_1437_);
lean_dec(v___x_1437_);
lean_dec_ref(v_val_1433_);
v___x_1439_ = lean_apply_2(v_toPure_1431_, lean_box(0), v___x_1438_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object* v_m_1468_, lean_object* v_inst_1469_, lean_object* v_inst_1470_, lean_object* v_stx_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_getDocStringText___redArg(v_inst_1469_, v_inst_1470_, v_stx_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT uint8_t l_Lean_isVersoDocComment(lean_object* v_stx_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1479_ = lean_unsigned_to_nat(1u);
v___x_1480_ = l_Lean_Syntax_getArg(v_stx_1478_, v___x_1479_);
v___x_1481_ = ((lean_object*)(l_Lean_isVersoDocComment___closed__0));
v___x_1482_ = l_Lean_Syntax_isOfKind(v___x_1480_, v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_isVersoDocComment___boxed(lean_object* v_stx_1483_){
_start:
{
uint8_t v_res_1484_; lean_object* v_r_1485_; 
v_res_1484_ = l_Lean_isVersoDocComment(v_stx_1483_);
lean_dec(v_stx_1483_);
v_r_1485_ = lean_box(v_res_1484_);
return v_r_1485_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_1489_ = ((lean_object*)(l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0));
v___x_1490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
lean_ctor_set(v___x_1490_, 2, v___x_1488_);
return v___x_1490_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default(void){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_obj_once(&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1, &l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1_once, _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1);
return v___x_1491_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet(void){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_nat_to_int(v_a_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_unsigned_to_nat(2u);
v___x_1502_ = lean_nat_to_int(v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_unsigned_to_nat(1u);
v___x_1504_ = lean_nat_to_int(v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object* v_x_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_){
_start:
{
if (lean_obj_tag(v_x_1519_) == 0)
{
lean_dec(v_x_1517_);
return v_x_1518_;
}
else
{
lean_object* v_head_1520_; lean_object* v_tail_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1532_; 
v_head_1520_ = lean_ctor_get(v_x_1519_, 0);
v_tail_1521_ = lean_ctor_get(v_x_1519_, 1);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1523_ = v_x_1519_;
v_isShared_1524_ = v_isSharedCheck_1532_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_tail_1521_);
lean_inc(v_head_1520_);
lean_dec(v_x_1519_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1532_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
lean_inc(v_x_1517_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set_tag(v___x_1523_, 5);
lean_ctor_set(v___x_1523_, 1, v_x_1517_);
lean_ctor_set(v___x_1523_, 0, v_x_1518_);
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_x_1518_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_x_1517_);
v___x_1526_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_1520_, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1526_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v_x_1518_ = v___x_1529_;
v_x_1519_ = v_tail_1521_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object* v_x_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_){
_start:
{
if (lean_obj_tag(v_x_1535_) == 0)
{
lean_dec(v_x_1533_);
return v_x_1534_;
}
else
{
lean_object* v_head_1536_; lean_object* v_tail_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1548_; 
v_head_1536_ = lean_ctor_get(v_x_1535_, 0);
v_tail_1537_ = lean_ctor_get(v_x_1535_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_x_1535_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1539_ = v_x_1535_;
v_isShared_1540_ = v_isSharedCheck_1548_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_tail_1537_);
lean_inc(v_head_1536_);
lean_dec(v_x_1535_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1548_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
lean_inc(v_x_1533_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 5);
lean_ctor_set(v___x_1539_, 1, v_x_1533_);
lean_ctor_set(v___x_1539_, 0, v_x_1534_);
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_x_1534_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_x_1533_);
v___x_1542_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1543_ = lean_unsigned_to_nat(0u);
v___x_1544_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_1536_, v___x_1543_);
v___x_1545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1542_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(v_x_1533_, v___x_1545_, v_tail_1537_);
return v___x_1546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_1549_, lean_object* v_x_1550_){
_start:
{
if (lean_obj_tag(v_x_1549_) == 0)
{
lean_object* v___x_1551_; 
lean_dec(v_x_1550_);
v___x_1551_ = lean_box(0);
return v___x_1551_;
}
else
{
lean_object* v_tail_1552_; 
v_tail_1552_ = lean_ctor_get(v_x_1549_, 1);
if (lean_obj_tag(v_tail_1552_) == 0)
{
lean_object* v_head_1553_; lean_object* v___x_1554_; 
lean_dec(v_x_1550_);
v_head_1553_ = lean_ctor_get(v_x_1549_, 0);
lean_inc(v_head_1553_);
lean_dec_ref_known(v_x_1549_, 2);
v___x_1554_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_1553_);
return v___x_1554_;
}
else
{
lean_object* v_head_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_inc(v_tail_1552_);
v_head_1555_ = lean_ctor_get(v_x_1549_, 0);
lean_inc(v_head_1555_);
lean_dec_ref_known(v_x_1549_, 2);
v___x_1556_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_1555_);
v___x_1557_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(v_x_1550_, v___x_1556_, v_tail_1552_);
return v___x_1557_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0));
v___x_1560_ = lean_string_length(v___x_1559_);
return v___x_1560_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_1562_ = lean_nat_to_int(v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_xs_1571_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1572_ = lean_array_get_size(v_xs_1571_);
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_nat_dec_eq(v___x_1572_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1575_ = lean_array_to_list(v_xs_1571_);
v___x_1576_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_1577_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_1575_, v___x_1576_);
v___x_1578_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_1579_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_1580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v___x_1577_);
v___x_1581_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1578_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = l_Std_Format_fill(v___x_1583_);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; 
lean_dec_ref(v_xs_1571_);
v___x_1585_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1640_, lean_object* v_prec_1641_){
_start:
{
switch(lean_obj_tag(v_x_1640_))
{
case 0:
{
lean_object* v_string_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1662_; 
v_string_1642_ = lean_ctor_get(v_x_1640_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_x_1640_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1644_ = v_x_1640_;
v_isShared_1645_ = v_isSharedCheck_1662_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_string_1642_);
lean_dec(v_x_1640_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1662_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___y_1647_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1658_ = lean_unsigned_to_nat(1024u);
v___x_1659_ = lean_nat_dec_le(v___x_1658_, v_prec_1641_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1647_ = v___x_1660_;
goto v___jp_1646_;
}
else
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1647_ = v___x_1661_;
goto v___jp_1646_;
}
v___jp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1648_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_1649_ = l_String_quote(v_string_1642_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set_tag(v___x_1644_, 3);
lean_ctor_set(v___x_1644_, 0, v___x_1649_);
v___x_1651_ = v___x_1644_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1648_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
lean_inc(v___y_1647_);
v___x_1653_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___y_1647_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = 0;
v___x_1655_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set_uint8(v___x_1655_, sizeof(void*)*1, v___x_1654_);
v___x_1656_ = l_Repr_addAppParen(v___x_1655_, v_prec_1641_);
return v___x_1656_;
}
}
}
}
case 1:
{
lean_object* v_content_1663_; lean_object* v___y_1665_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v_content_1663_ = lean_ctor_get(v_x_1640_, 0);
lean_inc_ref(v_content_1663_);
lean_dec_ref_known(v_x_1640_, 1);
v___x_1673_ = lean_unsigned_to_nat(1024u);
v___x_1674_ = lean_nat_dec_le(v___x_1673_, v_prec_1641_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1665_ = v___x_1675_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1665_ = v___x_1676_;
goto v___jp_1664_;
}
v___jp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1666_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7));
v___x_1667_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_1663_);
v___x_1668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
lean_inc(v___y_1665_);
v___x_1669_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___y_1665_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = 0;
v___x_1671_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*1, v___x_1670_);
v___x_1672_ = l_Repr_addAppParen(v___x_1671_, v_prec_1641_);
return v___x_1672_;
}
}
case 2:
{
lean_object* v_content_1677_; lean_object* v___y_1679_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_content_1677_ = lean_ctor_get(v_x_1640_, 0);
lean_inc_ref(v_content_1677_);
lean_dec_ref_known(v_x_1640_, 1);
v___x_1687_ = lean_unsigned_to_nat(1024u);
v___x_1688_ = lean_nat_dec_le(v___x_1687_, v_prec_1641_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1679_ = v___x_1689_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1679_ = v___x_1690_;
goto v___jp_1678_;
}
v___jp_1678_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1680_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10));
v___x_1681_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_1677_);
v___x_1682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
lean_inc(v___y_1679_);
v___x_1683_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___y_1679_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = 0;
v___x_1685_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set_uint8(v___x_1685_, sizeof(void*)*1, v___x_1684_);
v___x_1686_ = l_Repr_addAppParen(v___x_1685_, v_prec_1641_);
return v___x_1686_;
}
}
case 3:
{
lean_object* v_string_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1711_; 
v_string_1691_ = lean_ctor_get(v_x_1640_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_x_1640_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1693_ = v_x_1640_;
v_isShared_1694_ = v_isSharedCheck_1711_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_string_1691_);
lean_dec(v_x_1640_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1711_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___y_1696_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = lean_unsigned_to_nat(1024u);
v___x_1708_ = lean_nat_dec_le(v___x_1707_, v_prec_1641_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1696_ = v___x_1709_;
goto v___jp_1695_;
}
else
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1696_ = v___x_1710_;
goto v___jp_1695_;
}
v___jp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1697_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13));
v___x_1698_ = l_String_quote(v_string_1691_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1698_);
v___x_1700_ = v___x_1693_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1697_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
lean_inc(v___y_1696_);
v___x_1702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___y_1696_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = 0;
v___x_1704_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*1, v___x_1703_);
v___x_1705_ = l_Repr_addAppParen(v___x_1704_, v_prec_1641_);
return v___x_1705_;
}
}
}
}
case 4:
{
uint8_t v_mode_1712_; lean_object* v_string_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1738_; 
v_mode_1712_ = lean_ctor_get_uint8(v_x_1640_, sizeof(void*)*1);
v_string_1713_ = lean_ctor_get(v_x_1640_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_x_1640_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1715_ = v_x_1640_;
v_isShared_1716_ = v_isSharedCheck_1738_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_string_1713_);
lean_dec(v_x_1640_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1738_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___y_1718_; lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = lean_unsigned_to_nat(1024u);
v___x_1735_ = lean_nat_dec_le(v___x_1734_, v_prec_1641_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1718_ = v___x_1736_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1718_ = v___x_1737_;
goto v___jp_1717_;
}
v___jp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; lean_object* v___x_1731_; 
v___x_1719_ = lean_box(1);
v___x_1720_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16));
v___x_1721_ = lean_unsigned_to_nat(1024u);
v___x_1722_ = l_Lean_Doc_instReprMathMode_repr(v_mode_1712_, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1720_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v___x_1719_);
v___x_1725_ = l_String_quote(v_string_1713_);
v___x_1726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
v___x_1727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1724_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
lean_inc(v___y_1718_);
v___x_1728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___y_1718_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = 0;
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 6);
lean_ctor_set(v___x_1715_, 0, v___x_1728_);
v___x_1731_ = v___x_1715_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1728_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; 
lean_ctor_set_uint8(v___x_1731_, sizeof(void*)*1, v___x_1729_);
v___x_1732_ = l_Repr_addAppParen(v___x_1731_, v_prec_1641_);
return v___x_1732_;
}
}
}
}
case 5:
{
lean_object* v_string_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1759_; 
v_string_1739_ = lean_ctor_get(v_x_1640_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_x_1640_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1741_ = v_x_1640_;
v_isShared_1742_ = v_isSharedCheck_1759_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_string_1739_);
lean_dec(v_x_1640_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1759_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___y_1744_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = lean_unsigned_to_nat(1024u);
v___x_1756_ = lean_nat_dec_le(v___x_1755_, v_prec_1641_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1744_ = v___x_1757_;
goto v___jp_1743_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1744_ = v___x_1758_;
goto v___jp_1743_;
}
v___jp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1745_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19));
v___x_1746_ = l_String_quote(v_string_1739_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 3);
lean_ctor_set(v___x_1741_, 0, v___x_1746_);
v___x_1748_ = v___x_1741_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1745_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
lean_inc(v___y_1744_);
v___x_1750_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___y_1744_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = 0;
v___x_1752_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1752_, 0, v___x_1750_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*1, v___x_1751_);
v___x_1753_ = l_Repr_addAppParen(v___x_1752_, v_prec_1641_);
return v___x_1753_;
}
}
}
}
case 6:
{
lean_object* v_content_1760_; lean_object* v_url_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1785_; 
v_content_1760_ = lean_ctor_get(v_x_1640_, 0);
v_url_1761_ = lean_ctor_get(v_x_1640_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_x_1640_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1763_ = v_x_1640_;
v_isShared_1764_ = v_isSharedCheck_1785_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_url_1761_);
lean_inc(v_content_1760_);
lean_dec(v_x_1640_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1785_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___y_1766_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = lean_unsigned_to_nat(1024u);
v___x_1782_ = lean_nat_dec_le(v___x_1781_, v_prec_1641_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1766_ = v___x_1783_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1766_ = v___x_1784_;
goto v___jp_1765_;
}
v___jp_1765_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1767_ = lean_box(1);
v___x_1768_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22));
v___x_1769_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_1760_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set_tag(v___x_1763_, 5);
lean_ctor_set(v___x_1763_, 1, v___x_1769_);
lean_ctor_set(v___x_1763_, 0, v___x_1768_);
v___x_1771_ = v___x_1763_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___x_1767_);
v___x_1773_ = l_String_quote(v_url_1761_);
v___x_1774_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
v___x_1775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1772_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
lean_inc(v___y_1766_);
v___x_1776_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___y_1766_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = 0;
v___x_1778_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*1, v___x_1777_);
v___x_1779_ = l_Repr_addAppParen(v___x_1778_, v_prec_1641_);
return v___x_1779_;
}
}
}
}
case 7:
{
lean_object* v_name_1786_; lean_object* v_content_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1811_; 
v_name_1786_ = lean_ctor_get(v_x_1640_, 0);
v_content_1787_ = lean_ctor_get(v_x_1640_, 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_x_1640_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1789_ = v_x_1640_;
v_isShared_1790_ = v_isSharedCheck_1811_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_content_1787_);
lean_inc(v_name_1786_);
lean_dec(v_x_1640_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1811_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___y_1792_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = lean_unsigned_to_nat(1024u);
v___x_1808_ = lean_nat_dec_le(v___x_1807_, v_prec_1641_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1792_ = v___x_1809_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1792_ = v___x_1810_;
goto v___jp_1791_;
}
v___jp_1791_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1793_ = lean_box(1);
v___x_1794_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25));
v___x_1795_ = l_String_quote(v_name_1786_);
v___x_1796_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 5);
lean_ctor_set(v___x_1789_, 1, v___x_1796_);
lean_ctor_set(v___x_1789_, 0, v___x_1794_);
v___x_1798_ = v___x_1789_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1794_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v___x_1793_);
v___x_1800_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_1787_);
v___x_1801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
lean_inc(v___y_1792_);
v___x_1802_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___y_1792_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = 0;
v___x_1804_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*1, v___x_1803_);
v___x_1805_ = l_Repr_addAppParen(v___x_1804_, v_prec_1641_);
return v___x_1805_;
}
}
}
}
case 8:
{
lean_object* v_alt_1812_; lean_object* v_url_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1838_; 
v_alt_1812_ = lean_ctor_get(v_x_1640_, 0);
v_url_1813_ = lean_ctor_get(v_x_1640_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_x_1640_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1815_ = v_x_1640_;
v_isShared_1816_ = v_isSharedCheck_1838_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_url_1813_);
lean_inc(v_alt_1812_);
lean_dec(v_x_1640_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1838_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___y_1818_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = lean_unsigned_to_nat(1024u);
v___x_1835_ = lean_nat_dec_le(v___x_1834_, v_prec_1641_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1818_ = v___x_1836_;
goto v___jp_1817_;
}
else
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1818_ = v___x_1837_;
goto v___jp_1817_;
}
v___jp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1819_ = lean_box(1);
v___x_1820_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28));
v___x_1821_ = l_String_quote(v_alt_1812_);
v___x_1822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set_tag(v___x_1815_, 5);
lean_ctor_set(v___x_1815_, 1, v___x_1822_);
lean_ctor_set(v___x_1815_, 0, v___x_1820_);
v___x_1824_ = v___x_1815_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v___x_1819_);
v___x_1826_ = l_String_quote(v_url_1813_);
v___x_1827_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1825_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
lean_inc(v___y_1818_);
v___x_1829_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___y_1818_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = 0;
v___x_1831_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*1, v___x_1830_);
v___x_1832_ = l_Repr_addAppParen(v___x_1831_, v_prec_1641_);
return v___x_1832_;
}
}
}
}
case 9:
{
lean_object* v_content_1839_; lean_object* v___y_1841_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v_content_1839_ = lean_ctor_get(v_x_1640_, 0);
lean_inc_ref(v_content_1839_);
lean_dec_ref_known(v_x_1640_, 1);
v___x_1849_ = lean_unsigned_to_nat(1024u);
v___x_1850_ = lean_nat_dec_le(v___x_1849_, v_prec_1641_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1841_ = v___x_1851_;
goto v___jp_1840_;
}
else
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1841_ = v___x_1852_;
goto v___jp_1840_;
}
v___jp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1842_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31));
v___x_1843_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_1839_);
v___x_1844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
lean_inc(v___y_1841_);
v___x_1845_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___y_1841_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = 0;
v___x_1847_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*1, v___x_1846_);
v___x_1848_ = l_Repr_addAppParen(v___x_1847_, v_prec_1641_);
return v___x_1848_;
}
}
default: 
{
lean_object* v_container_1853_; lean_object* v_content_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1887_; 
v_container_1853_ = lean_ctor_get(v_x_1640_, 0);
v_content_1854_ = lean_ctor_get(v_x_1640_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_x_1640_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1856_ = v_x_1640_;
v_isShared_1857_ = v_isSharedCheck_1887_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_content_1854_);
lean_inc(v_container_1853_);
lean_dec(v_x_1640_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1887_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___y_1859_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1883_ = lean_unsigned_to_nat(1024u);
v___x_1884_ = lean_nat_dec_le(v___x_1883_, v_prec_1641_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1859_ = v___x_1885_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1859_ = v___x_1886_;
goto v___jp_1858_;
}
v___jp_1858_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1860_ = lean_box(1);
v___x_1861_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34));
v___x_1862_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__5));
v___x_1863_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_container_1853_);
lean_dec(v_container_1853_);
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = l_Lean_Name_reprPrec(v___x_1863_, v___x_1864_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set_tag(v___x_1856_, 5);
lean_ctor_set(v___x_1856_, 1, v___x_1865_);
lean_ctor_set(v___x_1856_, 0, v___x_1862_);
v___x_1867_ = v___x_1856_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1862_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1868_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__7));
v___x_1869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = l_Std_Format_nestD(v___x_1869_);
v___x_1871_ = 0;
v___x_1872_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*1, v___x_1871_);
v___x_1873_ = l_Std_Format_nestD(v___x_1872_);
v___x_1874_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set_uint8(v___x_1874_, sizeof(void*)*1, v___x_1871_);
v___x_1875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1861_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1860_);
v___x_1877_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_1854_);
v___x_1878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
lean_inc(v___y_1859_);
v___x_1879_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___y_1859_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set_uint8(v___x_1880_, sizeof(void*)*1, v___x_1871_);
v___x_1881_ = l_Repr_addAppParen(v___x_1880_, v_prec_1641_);
return v___x_1881_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v___y_1888_, v___x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_1891_, lean_object* v_prec_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_x_1891_, v_prec_1892_);
lean_dec(v_prec_1892_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object* v_xs_1894_){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1895_ = lean_array_get_size(v_xs_1894_);
v___x_1896_ = lean_unsigned_to_nat(0u);
v___x_1897_ = lean_nat_dec_eq(v___x_1895_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1898_ = lean_array_to_list(v_xs_1894_);
v___x_1899_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_1900_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_1898_, v___x_1899_);
v___x_1901_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_1902_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_1903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v___x_1900_);
v___x_1904_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_1905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1901_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = l_Std_Format_fill(v___x_1906_);
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; 
lean_dec_ref(v_xs_1894_);
v___x_1908_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_1908_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_unsigned_to_nat(12u);
v___x_1940_ = lean_nat_to_int(v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object* v_x_1941_, lean_object* v_x_1942_, lean_object* v_x_1943_){
_start:
{
if (lean_obj_tag(v_x_1943_) == 0)
{
lean_dec(v_x_1941_);
return v_x_1942_;
}
else
{
lean_object* v_head_1944_; lean_object* v_tail_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1956_; 
v_head_1944_ = lean_ctor_get(v_x_1943_, 0);
v_tail_1945_ = lean_ctor_get(v_x_1943_, 1);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_x_1943_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1947_ = v_x_1943_;
v_isShared_1948_ = v_isSharedCheck_1956_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_tail_1945_);
lean_inc(v_head_1944_);
lean_dec(v_x_1943_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1956_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
lean_inc(v_x_1941_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set_tag(v___x_1947_, 5);
lean_ctor_set(v___x_1947_, 1, v_x_1941_);
lean_ctor_set(v___x_1947_, 0, v_x_1942_);
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_x_1942_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_x_1941_);
v___x_1950_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = lean_unsigned_to_nat(0u);
v___x_1952_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_1944_, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1950_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v_x_1942_ = v___x_1953_;
v_x_1943_ = v_tail_1945_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object* v_x_1957_, lean_object* v_x_1958_, lean_object* v_x_1959_){
_start:
{
if (lean_obj_tag(v_x_1959_) == 0)
{
lean_dec(v_x_1957_);
return v_x_1958_;
}
else
{
lean_object* v_head_1960_; lean_object* v_tail_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1972_; 
v_head_1960_ = lean_ctor_get(v_x_1959_, 0);
v_tail_1961_ = lean_ctor_get(v_x_1959_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_x_1959_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1963_ = v_x_1959_;
v_isShared_1964_ = v_isSharedCheck_1972_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_tail_1961_);
lean_inc(v_head_1960_);
lean_dec(v_x_1959_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1972_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
lean_inc(v_x_1957_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set_tag(v___x_1963_, 5);
lean_ctor_set(v___x_1963_, 1, v_x_1957_);
lean_ctor_set(v___x_1963_, 0, v_x_1958_);
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_x_1958_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_x_1957_);
v___x_1966_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_1960_, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1966_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(v_x_1957_, v___x_1969_, v_tail_1961_);
return v___x_1970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object* v_x_1973_, lean_object* v_x_1974_){
_start:
{
if (lean_obj_tag(v_x_1973_) == 0)
{
lean_object* v___x_1975_; 
lean_dec(v_x_1974_);
v___x_1975_ = lean_box(0);
return v___x_1975_;
}
else
{
lean_object* v_tail_1976_; 
v_tail_1976_ = lean_ctor_get(v_x_1973_, 1);
if (lean_obj_tag(v_tail_1976_) == 0)
{
lean_object* v_head_1977_; lean_object* v___x_1978_; 
lean_dec(v_x_1974_);
v_head_1977_ = lean_ctor_get(v_x_1973_, 0);
lean_inc(v_head_1977_);
lean_dec_ref_known(v_x_1973_, 2);
v___x_1978_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_1977_);
return v___x_1978_;
}
else
{
lean_object* v_head_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_inc(v_tail_1976_);
v_head_1979_ = lean_ctor_get(v_x_1973_, 0);
lean_inc(v_head_1979_);
lean_dec_ref_known(v_x_1973_, 2);
v___x_1980_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_1979_);
v___x_1981_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(v_x_1974_, v___x_1980_, v_tail_1976_);
return v___x_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object* v_xs_1982_){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1983_ = lean_array_get_size(v_xs_1982_);
v___x_1984_ = lean_unsigned_to_nat(0u);
v___x_1985_ = lean_nat_dec_eq(v___x_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1986_ = lean_array_to_list(v_xs_1982_);
v___x_1987_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_1988_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_1986_, v___x_1987_);
v___x_1989_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_1990_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_1991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v___x_1988_);
v___x_1992_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_1993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1989_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = l_Std_Format_fill(v___x_1994_);
return v___x_1995_;
}
else
{
lean_object* v___x_1996_; 
lean_dec_ref(v_xs_1982_);
v___x_1996_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_1996_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_1999_ = lean_string_length(v___x_1998_);
return v___x_1999_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9);
v___x_2001_ = lean_nat_to_int(v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_x_2007_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2008_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6));
v___x_2009_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_2010_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_x_2007_);
v___x_2011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = 0;
v___x_2013_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*1, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2008_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2016_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v___x_2014_);
v___x_2018_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2015_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*1, v___x_2012_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object* v_x_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_){
_start:
{
if (lean_obj_tag(v_x_2024_) == 0)
{
lean_dec(v_x_2022_);
return v_x_2023_;
}
else
{
lean_object* v_head_2025_; lean_object* v_tail_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2036_; 
v_head_2025_ = lean_ctor_get(v_x_2024_, 0);
v_tail_2026_ = lean_ctor_get(v_x_2024_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_x_2024_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2028_ = v_x_2024_;
v_isShared_2029_ = v_isSharedCheck_2036_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_tail_2026_);
lean_inc(v_head_2025_);
lean_dec(v_x_2024_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2036_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
lean_inc(v_x_2022_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 5);
lean_ctor_set(v___x_2028_, 1, v_x_2022_);
lean_ctor_set(v___x_2028_, 0, v_x_2023_);
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_x_2023_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_x_2022_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2025_);
v___x_2033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v_x_2023_ = v___x_2033_;
v_x_2024_ = v_tail_2026_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object* v_x_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_){
_start:
{
if (lean_obj_tag(v_x_2039_) == 0)
{
lean_dec(v_x_2037_);
return v_x_2038_;
}
else
{
lean_object* v_head_2040_; lean_object* v_tail_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2051_; 
v_head_2040_ = lean_ctor_get(v_x_2039_, 0);
v_tail_2041_ = lean_ctor_get(v_x_2039_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_x_2039_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2043_ = v_x_2039_;
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_tail_2041_);
lean_inc(v_head_2040_);
lean_dec(v_x_2039_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
lean_inc(v_x_2037_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 5);
lean_ctor_set(v___x_2043_, 1, v_x_2037_);
lean_ctor_set(v___x_2043_, 0, v_x_2038_);
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_x_2038_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_x_2037_);
v___x_2046_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2040_);
v___x_2048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(v_x_2037_, v___x_2048_, v_tail_2041_);
return v___x_2049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_2052_, lean_object* v_x_2053_){
_start:
{
if (lean_obj_tag(v_x_2052_) == 0)
{
lean_object* v___x_2054_; 
lean_dec(v_x_2053_);
v___x_2054_ = lean_box(0);
return v___x_2054_;
}
else
{
lean_object* v_tail_2055_; 
v_tail_2055_ = lean_ctor_get(v_x_2052_, 1);
if (lean_obj_tag(v_tail_2055_) == 0)
{
lean_object* v_head_2056_; lean_object* v___x_2057_; 
lean_dec(v_x_2053_);
v_head_2056_ = lean_ctor_get(v_x_2052_, 0);
lean_inc(v_head_2056_);
lean_dec_ref_known(v_x_2052_, 2);
v___x_2057_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2056_);
return v___x_2057_;
}
else
{
lean_object* v_head_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_inc(v_tail_2055_);
v_head_2058_ = lean_ctor_get(v_x_2052_, 0);
lean_inc(v_head_2058_);
lean_dec_ref_known(v_x_2052_, 2);
v___x_2059_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2058_);
v___x_2060_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(v_x_2053_, v___x_2059_, v_tail_2055_);
return v___x_2060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object* v_xs_2061_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2062_ = lean_array_get_size(v_xs_2061_);
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = lean_nat_dec_eq(v___x_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2065_ = lean_array_to_list(v_xs_2061_);
v___x_2066_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2067_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(v___x_2065_, v___x_2066_);
v___x_2068_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2069_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___x_2067_);
v___x_2071_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2068_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = l_Std_Format_fill(v___x_2073_);
return v___x_2074_;
}
else
{
lean_object* v___x_2075_; 
lean_dec_ref(v_xs_2061_);
v___x_2075_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2075_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = lean_nat_to_int(v___x_2082_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_unsigned_to_nat(8u);
v___x_2100_ = lean_nat_to_int(v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_x_2104_){
_start:
{
lean_object* v_term_2105_; lean_object* v_desc_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2138_; 
v_term_2105_ = lean_ctor_get(v_x_2104_, 0);
v_desc_2106_ = lean_ctor_get(v_x_2104_, 1);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_x_2104_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2108_ = v_x_2104_;
v_isShared_2109_ = v_isSharedCheck_2138_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_desc_2106_);
lean_inc(v_term_2105_);
lean_dec(v_x_2104_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2138_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2110_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_2111_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3));
v___x_2112_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_2113_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_term_2105_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set_tag(v___x_2108_, 4);
lean_ctor_set(v___x_2108_, 1, v___x_2113_);
lean_ctor_set(v___x_2108_, 0, v___x_2112_);
v___x_2115_ = v___x_2108_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
uint8_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2116_ = 0;
v___x_2117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*1, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2111_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_2120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_box(1);
v___x_2122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6));
v___x_2124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v___x_2110_);
v___x_2126_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_desc_2106_);
v___x_2127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2112_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set_uint8(v___x_2128_, sizeof(void*)*1, v___x_2116_);
v___x_2129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2125_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2131_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___x_2129_);
v___x_2133_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2132_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2130_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*1, v___x_2116_);
return v___x_2136_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object* v_x_2139_, lean_object* v_x_2140_, lean_object* v_x_2141_){
_start:
{
if (lean_obj_tag(v_x_2141_) == 0)
{
lean_dec(v_x_2139_);
return v_x_2140_;
}
else
{
lean_object* v_head_2142_; lean_object* v_tail_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2153_; 
v_head_2142_ = lean_ctor_get(v_x_2141_, 0);
v_tail_2143_ = lean_ctor_get(v_x_2141_, 1);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_x_2141_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2145_ = v_x_2141_;
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_tail_2143_);
lean_inc(v_head_2142_);
lean_dec(v_x_2141_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
lean_inc(v_x_2139_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set_tag(v___x_2145_, 5);
lean_ctor_set(v___x_2145_, 1, v_x_2139_);
lean_ctor_set(v___x_2145_, 0, v_x_2140_);
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_x_2140_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_x_2139_);
v___x_2148_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2142_);
v___x_2150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v_x_2140_ = v___x_2150_;
v_x_2141_ = v_tail_2143_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
if (lean_obj_tag(v_x_2156_) == 0)
{
lean_dec(v_x_2154_);
return v_x_2155_;
}
else
{
lean_object* v_head_2157_; lean_object* v_tail_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2168_; 
v_head_2157_ = lean_ctor_get(v_x_2156_, 0);
v_tail_2158_ = lean_ctor_get(v_x_2156_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_x_2156_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2160_ = v_x_2156_;
v_isShared_2161_ = v_isSharedCheck_2168_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_tail_2158_);
lean_inc(v_head_2157_);
lean_dec(v_x_2156_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2168_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
lean_inc(v_x_2154_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set_tag(v___x_2160_, 5);
lean_ctor_set(v___x_2160_, 1, v_x_2154_);
lean_ctor_set(v___x_2160_, 0, v_x_2155_);
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_x_2155_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_x_2154_);
v___x_2163_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2157_);
v___x_2165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(v_x_2154_, v___x_2165_, v_tail_2158_);
return v___x_2166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 0)
{
lean_object* v___x_2171_; 
lean_dec(v_x_2170_);
v___x_2171_ = lean_box(0);
return v___x_2171_;
}
else
{
lean_object* v_tail_2172_; 
v_tail_2172_ = lean_ctor_get(v_x_2169_, 1);
if (lean_obj_tag(v_tail_2172_) == 0)
{
lean_object* v_head_2173_; lean_object* v___x_2174_; 
lean_dec(v_x_2170_);
v_head_2173_ = lean_ctor_get(v_x_2169_, 0);
lean_inc(v_head_2173_);
lean_dec_ref_known(v_x_2169_, 2);
v___x_2174_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2173_);
return v___x_2174_;
}
else
{
lean_object* v_head_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_inc(v_tail_2172_);
v_head_2175_ = lean_ctor_get(v_x_2169_, 0);
lean_inc(v_head_2175_);
lean_dec_ref_known(v_x_2169_, 2);
v___x_2176_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2175_);
v___x_2177_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(v_x_2170_, v___x_2176_, v_tail_2172_);
return v___x_2177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object* v_xs_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2179_ = lean_array_get_size(v_xs_2178_);
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = lean_nat_dec_eq(v___x_2179_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2182_ = lean_array_to_list(v_xs_2178_);
v___x_2183_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2184_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(v___x_2182_, v___x_2183_);
v___x_2185_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2186_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v___x_2184_);
v___x_2188_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2187_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2185_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = l_Std_Format_fill(v___x_2190_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; 
lean_dec_ref(v_xs_2178_);
v___x_2192_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object* v_x_2211_, lean_object* v_prec_2212_){
_start:
{
switch(lean_obj_tag(v_x_2211_))
{
case 0:
{
lean_object* v_contents_2213_; lean_object* v___y_2215_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_contents_2213_ = lean_ctor_get(v_x_2211_, 0);
lean_inc_ref(v_contents_2213_);
lean_dec_ref_known(v_x_2211_, 1);
v___x_2223_ = lean_unsigned_to_nat(1024u);
v___x_2224_ = lean_nat_dec_le(v___x_2223_, v_prec_2212_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2215_ = v___x_2225_;
goto v___jp_2214_;
}
else
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2215_ = v___x_2226_;
goto v___jp_2214_;
}
v___jp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2216_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2));
v___x_2217_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_contents_2213_);
v___x_2218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
lean_inc(v___y_2215_);
v___x_2219_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___y_2215_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = 0;
v___x_2221_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*1, v___x_2220_);
v___x_2222_ = l_Repr_addAppParen(v___x_2221_, v_prec_2212_);
return v___x_2222_;
}
}
case 1:
{
lean_object* v_content_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2247_; 
v_content_2227_ = lean_ctor_get(v_x_2211_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_x_2211_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2229_ = v_x_2211_;
v_isShared_2230_ = v_isSharedCheck_2247_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_content_2227_);
lean_dec(v_x_2211_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2247_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___y_2232_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = lean_unsigned_to_nat(1024u);
v___x_2244_ = lean_nat_dec_le(v___x_2243_, v_prec_2212_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2232_ = v___x_2245_;
goto v___jp_2231_;
}
else
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2232_ = v___x_2246_;
goto v___jp_2231_;
}
v___jp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2233_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5));
v___x_2234_ = l_String_quote(v_content_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set_tag(v___x_2229_, 3);
lean_ctor_set(v___x_2229_, 0, v___x_2234_);
v___x_2236_ = v___x_2229_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2233_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
lean_inc(v___y_2232_);
v___x_2238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___y_2232_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = 0;
v___x_2240_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*1, v___x_2239_);
v___x_2241_ = l_Repr_addAppParen(v___x_2240_, v_prec_2212_);
return v___x_2241_;
}
}
}
}
case 2:
{
lean_object* v_items_2248_; lean_object* v___y_2250_; lean_object* v___x_2258_; uint8_t v___x_2259_; 
v_items_2248_ = lean_ctor_get(v_x_2211_, 0);
lean_inc_ref(v_items_2248_);
lean_dec_ref_known(v_x_2211_, 1);
v___x_2258_ = lean_unsigned_to_nat(1024u);
v___x_2259_ = lean_nat_dec_le(v___x_2258_, v_prec_2212_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2250_ = v___x_2260_;
goto v___jp_2249_;
}
else
{
lean_object* v___x_2261_; 
v___x_2261_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2250_ = v___x_2261_;
goto v___jp_2249_;
}
v___jp_2249_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2251_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8));
v___x_2252_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_2248_);
v___x_2253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
lean_inc(v___y_2250_);
v___x_2254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___y_2250_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = 0;
v___x_2256_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*1, v___x_2255_);
v___x_2257_ = l_Repr_addAppParen(v___x_2256_, v_prec_2212_);
return v___x_2257_;
}
}
case 3:
{
lean_object* v_start_2262_; lean_object* v_items_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2298_; 
v_start_2262_ = lean_ctor_get(v_x_2211_, 0);
v_items_2263_ = lean_ctor_get(v_x_2211_, 1);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_x_2211_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2265_ = v_x_2211_;
v_isShared_2266_ = v_isSharedCheck_2298_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_items_2263_);
lean_inc(v_start_2262_);
lean_dec(v_x_2211_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2298_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2283_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2294_ = lean_unsigned_to_nat(1024u);
v___x_2295_ = lean_nat_dec_le(v___x_2294_, v_prec_2212_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2283_ = v___x_2296_;
goto v___jp_2282_;
}
else
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2283_ = v___x_2297_;
goto v___jp_2282_;
}
v___jp_2267_:
{
lean_object* v___x_2273_; 
lean_inc(v___y_2269_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set_tag(v___x_2265_, 5);
lean_ctor_set(v___x_2265_, 1, v___y_2271_);
lean_ctor_set(v___x_2265_, 0, v___y_2269_);
v___x_2273_ = v___x_2265_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___y_2269_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___y_2271_);
v___x_2273_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_inc(v___y_2270_);
v___x_2274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v___y_2270_);
v___x_2275_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_2263_);
v___x_2276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
lean_inc(v___y_2268_);
v___x_2277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___y_2268_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = 0;
v___x_2279_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set_uint8(v___x_2279_, sizeof(void*)*1, v___x_2278_);
v___x_2280_ = l_Repr_addAppParen(v___x_2279_, v_prec_2212_);
return v___x_2280_;
}
}
v___jp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2284_ = lean_box(1);
v___x_2285_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11));
v___x_2286_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12, &l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12);
v___x_2287_ = lean_int_dec_lt(v_start_2262_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = l_Int_repr(v_start_2262_);
lean_dec(v_start_2262_);
v___x_2289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
v___y_2268_ = v___y_2283_;
v___y_2269_ = v___x_2285_;
v___y_2270_ = v___x_2284_;
v___y_2271_ = v___x_2289_;
goto v___jp_2267_;
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2290_ = lean_unsigned_to_nat(1024u);
v___x_2291_ = l_Int_repr(v_start_2262_);
lean_dec(v_start_2262_);
v___x_2292_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
v___x_2293_ = l_Repr_addAppParen(v___x_2292_, v___x_2290_);
v___y_2268_ = v___y_2283_;
v___y_2269_ = v___x_2285_;
v___y_2270_ = v___x_2284_;
v___y_2271_ = v___x_2293_;
goto v___jp_2267_;
}
}
}
}
case 4:
{
lean_object* v_items_2299_; lean_object* v___y_2301_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v_items_2299_ = lean_ctor_get(v_x_2211_, 0);
lean_inc_ref(v_items_2299_);
lean_dec_ref_known(v_x_2211_, 1);
v___x_2309_ = lean_unsigned_to_nat(1024u);
v___x_2310_ = lean_nat_dec_le(v___x_2309_, v_prec_2212_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; 
v___x_2311_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2301_ = v___x_2311_;
goto v___jp_2300_;
}
else
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2301_ = v___x_2312_;
goto v___jp_2300_;
}
v___jp_2300_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2302_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15));
v___x_2303_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(v_items_2299_);
v___x_2304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
lean_inc(v___y_2301_);
v___x_2305_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___y_2301_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = 0;
v___x_2307_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*1, v___x_2306_);
v___x_2308_ = l_Repr_addAppParen(v___x_2307_, v_prec_2212_);
return v___x_2308_;
}
}
case 5:
{
lean_object* v_items_2313_; lean_object* v___y_2315_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v_items_2313_ = lean_ctor_get(v_x_2211_, 0);
lean_inc_ref(v_items_2313_);
lean_dec_ref_known(v_x_2211_, 1);
v___x_2323_ = lean_unsigned_to_nat(1024u);
v___x_2324_ = lean_nat_dec_le(v___x_2323_, v_prec_2212_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2315_ = v___x_2325_;
goto v___jp_2314_;
}
else
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2315_ = v___x_2326_;
goto v___jp_2314_;
}
v___jp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2316_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18));
v___x_2317_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_items_2313_);
v___x_2318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
lean_inc(v___y_2315_);
v___x_2319_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___y_2315_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = 0;
v___x_2321_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*1, v___x_2320_);
v___x_2322_ = l_Repr_addAppParen(v___x_2321_, v_prec_2212_);
return v___x_2322_;
}
}
case 6:
{
lean_object* v_content_2327_; lean_object* v___y_2329_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v_content_2327_ = lean_ctor_get(v_x_2211_, 0);
lean_inc_ref(v_content_2327_);
lean_dec_ref_known(v_x_2211_, 1);
v___x_2337_ = lean_unsigned_to_nat(1024u);
v___x_2338_ = lean_nat_dec_le(v___x_2337_, v_prec_2212_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; 
v___x_2339_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2329_ = v___x_2339_;
goto v___jp_2328_;
}
else
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2329_ = v___x_2340_;
goto v___jp_2328_;
}
v___jp_2328_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2330_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21));
v___x_2331_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_2327_);
v___x_2332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
lean_inc(v___y_2329_);
v___x_2333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___y_2329_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = 0;
v___x_2335_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*1, v___x_2334_);
v___x_2336_ = l_Repr_addAppParen(v___x_2335_, v_prec_2212_);
return v___x_2336_;
}
}
default: 
{
lean_object* v_container_2341_; lean_object* v_content_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2375_; 
v_container_2341_ = lean_ctor_get(v_x_2211_, 0);
v_content_2342_ = lean_ctor_get(v_x_2211_, 1);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_x_2211_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2344_ = v_x_2211_;
v_isShared_2345_ = v_isSharedCheck_2375_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_content_2342_);
lean_inc(v_container_2341_);
lean_dec(v_x_2211_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2375_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___y_2347_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2371_ = lean_unsigned_to_nat(1024u);
v___x_2372_ = lean_nat_dec_le(v___x_2371_, v_prec_2212_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2347_ = v___x_2373_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2347_ = v___x_2374_;
goto v___jp_2346_;
}
v___jp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2348_ = lean_box(1);
v___x_2349_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24));
v___x_2350_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__5));
v___x_2351_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_container_2341_);
lean_dec(v_container_2341_);
v___x_2352_ = lean_unsigned_to_nat(0u);
v___x_2353_ = l_Lean_Name_reprPrec(v___x_2351_, v___x_2352_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set_tag(v___x_2344_, 5);
lean_ctor_set(v___x_2344_, 1, v___x_2353_);
lean_ctor_set(v___x_2344_, 0, v___x_2350_);
v___x_2355_ = v___x_2344_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2356_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__7));
v___x_2357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = l_Std_Format_nestD(v___x_2357_);
v___x_2359_ = 0;
v___x_2360_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set_uint8(v___x_2360_, sizeof(void*)*1, v___x_2359_);
v___x_2361_ = l_Std_Format_nestD(v___x_2360_);
v___x_2362_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*1, v___x_2359_);
v___x_2363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2349_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
lean_ctor_set(v___x_2364_, 1, v___x_2348_);
v___x_2365_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_2342_);
v___x_2366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
lean_inc(v___y_2347_);
v___x_2367_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___y_2347_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*1, v___x_2359_);
v___x_2369_ = l_Repr_addAppParen(v___x_2368_, v_prec_2212_);
return v___x_2369_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object* v___y_2376_){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_unsigned_to_nat(0u);
v___x_2378_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v___y_2376_, v___x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object* v_x_2379_, lean_object* v_prec_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_x_2379_, v_prec_2380_);
lean_dec(v_prec_2380_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object* v_xs_2382_){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2383_ = lean_array_get_size(v_xs_2382_);
v___x_2384_ = lean_unsigned_to_nat(0u);
v___x_2385_ = lean_nat_dec_eq(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2386_ = lean_array_to_list(v_xs_2382_);
v___x_2387_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2388_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_2386_, v___x_2387_);
v___x_2389_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2390_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v___x_2388_);
v___x_2392_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2389_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = l_Std_Format_fill(v___x_2394_);
return v___x_2395_;
}
else
{
lean_object* v___x_2396_; 
lean_dec_ref(v_xs_2382_);
v___x_2396_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2396_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object* v_x_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = ((lean_object*)(l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1));
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_x_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_2402_);
lean_dec(v_x_2402_);
return v_res_2403_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_unsigned_to_nat(9u);
v___x_2414_ = lean_nat_to_int(v___x_2413_);
return v___x_2414_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = lean_unsigned_to_nat(15u);
v___x_2419_ = lean_nat_to_int(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = lean_unsigned_to_nat(11u);
v___x_2427_ = lean_nat_to_int(v___x_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object* v_x_2431_, lean_object* v_x_2432_, lean_object* v_x_2433_){
_start:
{
if (lean_obj_tag(v_x_2433_) == 0)
{
lean_dec(v_x_2431_);
return v_x_2432_;
}
else
{
lean_object* v_head_2434_; lean_object* v_tail_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2445_; 
v_head_2434_ = lean_ctor_get(v_x_2433_, 0);
v_tail_2435_ = lean_ctor_get(v_x_2433_, 1);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_x_2433_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2437_ = v_x_2433_;
v_isShared_2438_ = v_isSharedCheck_2445_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_tail_2435_);
lean_inc(v_head_2434_);
lean_dec(v_x_2433_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2445_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
lean_inc(v_x_2431_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set_tag(v___x_2437_, 5);
lean_ctor_set(v___x_2437_, 1, v_x_2431_);
lean_ctor_set(v___x_2437_, 0, v_x_2432_);
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_x_2432_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_x_2431_);
v___x_2440_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2434_);
v___x_2442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(v_x_2431_, v___x_2442_, v_tail_2435_);
return v___x_2443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
if (lean_obj_tag(v_x_2446_) == 0)
{
lean_object* v___x_2448_; 
lean_dec(v_x_2447_);
v___x_2448_ = lean_box(0);
return v___x_2448_;
}
else
{
lean_object* v_tail_2449_; 
v_tail_2449_ = lean_ctor_get(v_x_2446_, 1);
if (lean_obj_tag(v_tail_2449_) == 0)
{
lean_object* v_head_2450_; lean_object* v___x_2451_; 
lean_dec(v_x_2447_);
v_head_2450_ = lean_ctor_get(v_x_2446_, 0);
lean_inc(v_head_2450_);
lean_dec_ref_known(v_x_2446_, 2);
v___x_2451_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2450_);
return v___x_2451_;
}
else
{
lean_object* v_head_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
lean_inc(v_tail_2449_);
v_head_2452_ = lean_ctor_get(v_x_2446_, 0);
lean_inc(v_head_2452_);
lean_dec_ref_known(v_x_2446_, 2);
v___x_2453_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2452_);
v___x_2454_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(v_x_2447_, v___x_2453_, v_tail_2449_);
return v___x_2454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object* v_xs_2455_){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2456_ = lean_array_get_size(v_xs_2455_);
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = lean_nat_dec_eq(v___x_2456_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2459_ = lean_array_to_list(v_xs_2455_);
v___x_2460_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2461_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(v___x_2459_, v___x_2460_);
v___x_2462_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2463_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___x_2461_);
v___x_2465_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2462_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = l_Std_Format_fill(v___x_2467_);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; 
lean_dec_ref(v_xs_2455_);
v___x_2469_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object* v_x_2470_){
_start:
{
lean_object* v_title_2471_; lean_object* v_titleString_2472_; lean_object* v_metadata_2473_; lean_object* v_content_2474_; lean_object* v_subParts_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_title_2471_ = lean_ctor_get(v_x_2470_, 0);
lean_inc_ref(v_title_2471_);
v_titleString_2472_ = lean_ctor_get(v_x_2470_, 1);
lean_inc_ref(v_titleString_2472_);
v_metadata_2473_ = lean_ctor_get(v_x_2470_, 2);
lean_inc(v_metadata_2473_);
v_content_2474_ = lean_ctor_get(v_x_2470_, 3);
lean_inc_ref(v_content_2474_);
v_subParts_2475_ = lean_ctor_get(v_x_2470_, 4);
lean_inc_ref(v_subParts_2475_);
lean_dec_ref(v_x_2470_);
v___x_2476_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_2477_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3));
v___x_2478_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4);
v___x_2479_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_title_2471_);
v___x_2480_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2478_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = 0;
v___x_2482_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set_uint8(v___x_2482_, sizeof(void*)*1, v___x_2481_);
v___x_2483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2477_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_2485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_box(1);
v___x_2487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6));
v___x_2489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
lean_ctor_set(v___x_2490_, 1, v___x_2476_);
v___x_2491_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7);
v___x_2492_ = l_String_quote(v_titleString_2472_);
v___x_2493_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2491_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set_uint8(v___x_2495_, sizeof(void*)*1, v___x_2481_);
v___x_2496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2490_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___x_2484_);
v___x_2498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
lean_ctor_set(v___x_2498_, 1, v___x_2486_);
v___x_2499_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9));
v___x_2500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v___x_2476_);
v___x_2502_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_2503_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_metadata_2473_);
lean_dec(v_metadata_2473_);
v___x_2504_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2502_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
lean_ctor_set_uint8(v___x_2505_, sizeof(void*)*1, v___x_2481_);
v___x_2506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2501_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
lean_ctor_set(v___x_2507_, 1, v___x_2484_);
v___x_2508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
lean_ctor_set(v___x_2508_, 1, v___x_2486_);
v___x_2509_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11));
v___x_2510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2476_);
v___x_2512_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12);
v___x_2513_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_content_2474_);
v___x_2514_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
lean_ctor_set_uint8(v___x_2515_, sizeof(void*)*1, v___x_2481_);
v___x_2516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2511_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
lean_ctor_set(v___x_2517_, 1, v___x_2484_);
v___x_2518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
lean_ctor_set(v___x_2518_, 1, v___x_2486_);
v___x_2519_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14));
v___x_2520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v___x_2476_);
v___x_2522_ = l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(v_subParts_2475_);
v___x_2523_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2502_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
lean_ctor_set_uint8(v___x_2524_, sizeof(void*)*1, v___x_2481_);
v___x_2525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2521_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2527_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
lean_ctor_set(v___x_2528_, 1, v___x_2525_);
v___x_2529_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2528_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2526_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*1, v___x_2481_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object* v_x_2533_, lean_object* v_x_2534_, lean_object* v_x_2535_){
_start:
{
if (lean_obj_tag(v_x_2535_) == 0)
{
lean_dec(v_x_2533_);
return v_x_2534_;
}
else
{
lean_object* v_head_2536_; lean_object* v_tail_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2547_; 
v_head_2536_ = lean_ctor_get(v_x_2535_, 0);
v_tail_2537_ = lean_ctor_get(v_x_2535_, 1);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_x_2535_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2539_ = v_x_2535_;
v_isShared_2540_ = v_isSharedCheck_2547_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_tail_2537_);
lean_inc(v_head_2536_);
lean_dec(v_x_2535_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2547_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
lean_inc(v_x_2533_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set_tag(v___x_2539_, 5);
lean_ctor_set(v___x_2539_, 1, v_x_2533_);
lean_ctor_set(v___x_2539_, 0, v_x_2534_);
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_x_2534_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_x_2533_);
v___x_2542_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2536_);
v___x_2544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v_x_2534_ = v___x_2544_;
v_x_2535_ = v_tail_2537_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object* v_x_2548_, lean_object* v_x_2549_){
_start:
{
lean_object* v_fst_2550_; lean_object* v_snd_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2561_; 
v_fst_2550_ = lean_ctor_get(v_x_2548_, 0);
v_snd_2551_ = lean_ctor_get(v_x_2548_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_x_2548_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2553_ = v_x_2548_;
v_isShared_2554_ = v_isSharedCheck_2561_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_snd_2551_);
lean_inc(v_fst_2550_);
lean_dec(v_x_2548_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2561_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2555_ = l_Lean_instReprDeclarationRange_repr___redArg(v_fst_2550_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set_tag(v___x_2553_, 1);
lean_ctor_set(v___x_2553_, 1, v_x_2549_);
lean_ctor_set(v___x_2553_, 0, v___x_2555_);
v___x_2557_ = v___x_2553_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_x_2549_);
v___x_2557_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_snd_2551_);
v___x_2559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v___x_2557_);
return v___x_2559_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object* v_x_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_){
_start:
{
if (lean_obj_tag(v_x_2564_) == 0)
{
lean_dec(v_x_2562_);
return v_x_2563_;
}
else
{
lean_object* v_head_2565_; lean_object* v_tail_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2575_; 
v_head_2565_ = lean_ctor_get(v_x_2564_, 0);
v_tail_2566_ = lean_ctor_get(v_x_2564_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_x_2564_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2568_ = v_x_2564_;
v_isShared_2569_ = v_isSharedCheck_2575_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_tail_2566_);
lean_inc(v_head_2565_);
lean_dec(v_x_2564_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2575_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
lean_inc(v_x_2562_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 5);
lean_ctor_set(v___x_2568_, 1, v_x_2562_);
lean_ctor_set(v___x_2568_, 0, v_x_2563_);
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_x_2563_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_x_2562_);
v___x_2571_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v_head_2565_);
v_x_2563_ = v___x_2572_;
v_x_2564_ = v_tail_2566_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object* v_x_2576_, lean_object* v_x_2577_){
_start:
{
if (lean_obj_tag(v_x_2576_) == 0)
{
lean_object* v___x_2578_; 
lean_dec(v_x_2577_);
v___x_2578_ = lean_box(0);
return v___x_2578_;
}
else
{
lean_object* v_tail_2579_; 
v_tail_2579_ = lean_ctor_get(v_x_2576_, 1);
if (lean_obj_tag(v_tail_2579_) == 0)
{
lean_object* v_head_2580_; 
lean_dec(v_x_2577_);
v_head_2580_ = lean_ctor_get(v_x_2576_, 0);
lean_inc(v_head_2580_);
lean_dec_ref_known(v_x_2576_, 2);
return v_head_2580_;
}
else
{
lean_object* v_head_2581_; lean_object* v___x_2582_; 
lean_inc(v_tail_2579_);
v_head_2581_ = lean_ctor_get(v_x_2576_, 0);
lean_inc(v_head_2581_);
lean_dec_ref_known(v_x_2576_, 2);
v___x_2582_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(v_x_2577_, v_head_2581_, v_tail_2579_);
return v___x_2582_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0));
v___x_2586_ = lean_string_length(v___x_2585_);
return v___x_2586_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2);
v___x_2588_ = lean_nat_to_int(v___x_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object* v_x_2593_){
_start:
{
lean_object* v_fst_2594_; lean_object* v_snd_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2617_; 
v_fst_2594_ = lean_ctor_get(v_x_2593_, 0);
v_snd_2595_ = lean_ctor_get(v_x_2593_, 1);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_x_2593_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2597_ = v_x_2593_;
v_isShared_2598_ = v_isSharedCheck_2617_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_snd_2595_);
lean_inc(v_fst_2594_);
lean_dec(v_x_2593_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2617_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2599_ = l_Nat_reprFast(v_fst_2594_);
v___x_2600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
v___x_2601_ = lean_box(0);
if (v_isShared_2598_ == 0)
{
lean_ctor_set_tag(v___x_2597_, 1);
lean_ctor_set(v___x_2597_, 1, v___x_2601_);
lean_ctor_set(v___x_2597_, 0, v___x_2600_);
v___x_2603_ = v___x_2597_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; 
v___x_2604_ = l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(v_snd_2595_, v___x_2603_);
v___x_2605_ = l_List_reverse___redArg(v___x_2604_);
v___x_2606_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2607_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(v___x_2605_, v___x_2606_);
v___x_2608_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3);
v___x_2609_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4));
v___x_2610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___x_2607_);
v___x_2611_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__5));
v___x_2612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2610_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2608_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = 0;
v___x_2615_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*1, v___x_2614_);
return v___x_2615_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object* v_x_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_){
_start:
{
if (lean_obj_tag(v_x_2620_) == 0)
{
lean_dec(v_x_2618_);
return v_x_2619_;
}
else
{
lean_object* v_head_2621_; lean_object* v_tail_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2632_; 
v_head_2621_ = lean_ctor_get(v_x_2620_, 0);
v_tail_2622_ = lean_ctor_get(v_x_2620_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_x_2620_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2624_ = v_x_2620_;
v_isShared_2625_ = v_isSharedCheck_2632_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_tail_2622_);
lean_inc(v_head_2621_);
lean_dec(v_x_2620_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2632_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
lean_inc(v_x_2618_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 5);
lean_ctor_set(v___x_2624_, 1, v_x_2618_);
lean_ctor_set(v___x_2624_, 0, v_x_2619_);
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_x_2619_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_x_2618_);
v___x_2627_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_2621_);
v___x_2629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2627_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v_x_2619_ = v___x_2629_;
v_x_2620_ = v_tail_2622_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object* v_x_2633_, lean_object* v_x_2634_, lean_object* v_x_2635_){
_start:
{
if (lean_obj_tag(v_x_2635_) == 0)
{
lean_dec(v_x_2633_);
return v_x_2634_;
}
else
{
lean_object* v_head_2636_; lean_object* v_tail_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2647_; 
v_head_2636_ = lean_ctor_get(v_x_2635_, 0);
v_tail_2637_ = lean_ctor_get(v_x_2635_, 1);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_x_2635_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2639_ = v_x_2635_;
v_isShared_2640_ = v_isSharedCheck_2647_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_tail_2637_);
lean_inc(v_head_2636_);
lean_dec(v_x_2635_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2647_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
lean_inc(v_x_2633_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set_tag(v___x_2639_, 5);
lean_ctor_set(v___x_2639_, 1, v_x_2633_);
lean_ctor_set(v___x_2639_, 0, v_x_2634_);
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_x_2634_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_x_2633_);
v___x_2642_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_2636_);
v___x_2644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(v_x_2633_, v___x_2644_, v_tail_2637_);
return v___x_2645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object* v_x_2648_, lean_object* v_x_2649_){
_start:
{
if (lean_obj_tag(v_x_2648_) == 0)
{
lean_object* v___x_2650_; 
lean_dec(v_x_2649_);
v___x_2650_ = lean_box(0);
return v___x_2650_;
}
else
{
lean_object* v_tail_2651_; 
v_tail_2651_ = lean_ctor_get(v_x_2648_, 1);
if (lean_obj_tag(v_tail_2651_) == 0)
{
lean_object* v_head_2652_; lean_object* v___x_2653_; 
lean_dec(v_x_2649_);
v_head_2652_ = lean_ctor_get(v_x_2648_, 0);
lean_inc(v_head_2652_);
lean_dec_ref_known(v_x_2648_, 2);
v___x_2653_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_2652_);
return v___x_2653_;
}
else
{
lean_object* v_head_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_inc(v_tail_2651_);
v_head_2654_ = lean_ctor_get(v_x_2648_, 0);
lean_inc(v_head_2654_);
lean_dec_ref_known(v_x_2648_, 2);
v___x_2655_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_2654_);
v___x_2656_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(v_x_2649_, v___x_2655_, v_tail_2651_);
return v___x_2656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object* v_xs_2657_){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2658_ = lean_array_get_size(v_xs_2657_);
v___x_2659_ = lean_unsigned_to_nat(0u);
v___x_2660_ = lean_nat_dec_eq(v___x_2658_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2661_ = lean_array_to_list(v_xs_2657_);
v___x_2662_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2663_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(v___x_2661_, v___x_2662_);
v___x_2664_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2665_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v___x_2663_);
v___x_2667_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2664_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = l_Std_Format_fill(v___x_2669_);
return v___x_2670_;
}
else
{
lean_object* v___x_2671_; 
lean_dec_ref(v_xs_2657_);
v___x_2671_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2671_;
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = lean_unsigned_to_nat(20u);
v___x_2688_ = lean_nat_to_int(v___x_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object* v_x_2689_){
_start:
{
lean_object* v_text_2690_; lean_object* v_sections_2691_; lean_object* v_declarationRange_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v_text_2690_ = lean_ctor_get(v_x_2689_, 0);
lean_inc_ref(v_text_2690_);
v_sections_2691_ = lean_ctor_get(v_x_2689_, 1);
lean_inc_ref(v_sections_2691_);
v_declarationRange_2692_ = lean_ctor_get(v_x_2689_, 2);
lean_inc_ref(v_declarationRange_2692_);
lean_dec_ref(v_x_2689_);
v___x_2693_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_2694_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3));
v___x_2695_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_2696_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_text_2690_);
v___x_2697_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = 0;
v___x_2699_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*1, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2694_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_2702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = lean_box(1);
v___x_2704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5));
v___x_2706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
lean_ctor_set(v___x_2707_, 1, v___x_2693_);
v___x_2708_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_2709_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(v_sections_2691_);
v___x_2710_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set_uint8(v___x_2711_, sizeof(void*)*1, v___x_2698_);
v___x_2712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2707_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v___x_2701_);
v___x_2714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v___x_2703_);
v___x_2715_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7));
v___x_2716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v___x_2693_);
v___x_2718_ = lean_obj_once(&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8, &l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once, _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8);
v___x_2719_ = l_Lean_instReprDeclarationRange_repr___redArg(v_declarationRange_2692_);
v___x_2720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2718_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*1, v___x_2698_);
v___x_2722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2717_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v___x_2723_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2724_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v___x_2722_);
v___x_2726_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2725_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2723_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*1, v___x_2698_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object* v_x_2730_, lean_object* v_prec_2731_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(v_x_2730_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object* v_x_2733_, lean_object* v_prec_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_VersoModuleDocs_instReprSnippet_repr(v_x_2733_, v_prec_2734_);
lean_dec(v_prec_2734_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object* v_x_2736_, lean_object* v_x_2737_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_x_2736_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object* v_x_2739_, lean_object* v_x_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(v_x_2739_, v_x_2740_);
lean_dec(v_x_2740_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_2742_, lean_object* v_prec_2743_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_x_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_x_2745_, lean_object* v_prec_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(v_x_2745_, v_prec_2746_);
lean_dec(v_prec_2746_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object* v_x_2748_, lean_object* v_prec_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_x_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_x_2751_, lean_object* v_prec_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(v_x_2751_, v_prec_2752_);
lean_dec(v_prec_2752_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object* v_x_2754_, lean_object* v_x_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_2754_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object* v_x_2757_, lean_object* v_x_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(v_x_2757_, v_x_2758_);
lean_dec(v_x_2758_);
lean_dec(v_x_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object* v_x_2760_, lean_object* v_prec_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_x_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object* v_x_2763_, lean_object* v_prec_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(v_x_2763_, v_prec_2764_);
lean_dec(v_prec_2764_);
return v_res_2765_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object* v_level_2768_, lean_object* v_snippet_2769_){
_start:
{
lean_object* v_sections_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v_sections_2770_ = lean_ctor_get(v_snippet_2769_, 1);
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = lean_array_get_size(v_sections_2770_);
v___x_2773_ = lean_nat_dec_lt(v___x_2771_, v___x_2772_);
if (v___x_2773_ == 0)
{
uint8_t v___x_2774_; 
v___x_2774_ = 1;
return v___x_2774_;
}
else
{
lean_object* v___x_2775_; lean_object* v_fst_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2775_ = lean_array_fget_borrowed(v_sections_2770_, v___x_2771_);
v_fst_2776_ = lean_ctor_get(v___x_2775_, 0);
v___x_2777_ = lean_unsigned_to_nat(1u);
v___x_2778_ = lean_nat_add(v_level_2768_, v___x_2777_);
v___x_2779_ = lean_nat_dec_le(v_fst_2776_, v___x_2778_);
lean_dec(v___x_2778_);
return v___x_2779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object* v_level_2780_, lean_object* v_snippet_2781_){
_start:
{
uint8_t v_res_2782_; lean_object* v_r_2783_; 
v_res_2782_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_2780_, v_snippet_2781_);
lean_dec_ref(v_snippet_2781_);
lean_dec(v_level_2780_);
v_r_2783_ = lean_box(v_res_2782_);
return v_r_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object* v_snippet_2784_){
_start:
{
lean_object* v_sections_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v_sections_2785_ = lean_ctor_get(v_snippet_2784_, 1);
v___x_2786_ = lean_array_get_size(v_sections_2785_);
v___x_2787_ = lean_unsigned_to_nat(1u);
v___x_2788_ = lean_nat_sub(v___x_2786_, v___x_2787_);
v___x_2789_ = lean_nat_dec_lt(v___x_2788_, v___x_2786_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; 
lean_dec(v___x_2788_);
v___x_2790_ = lean_box(0);
return v___x_2790_;
}
else
{
lean_object* v___x_2791_; lean_object* v_fst_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_array_fget_borrowed(v_sections_2785_, v___x_2788_);
lean_dec(v___x_2788_);
v_fst_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_fst_2792_);
v___x_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_fst_2792_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object* v_snippet_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_2794_);
lean_dec_ref(v_snippet_2794_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object* v_snippet_2796_, lean_object* v_block_2797_){
_start:
{
lean_object* v_text_2798_; lean_object* v_sections_2799_; lean_object* v_declarationRange_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v_text_2798_ = lean_ctor_get(v_snippet_2796_, 0);
v_sections_2799_ = lean_ctor_get(v_snippet_2796_, 1);
v_declarationRange_2800_ = lean_ctor_get(v_snippet_2796_, 2);
v___x_2801_ = lean_array_get_size(v_sections_2799_);
v___x_2802_ = lean_unsigned_to_nat(0u);
v___x_2803_ = lean_nat_dec_eq(v___x_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2804_ = lean_unsigned_to_nat(1u);
v___x_2805_ = lean_nat_sub(v___x_2801_, v___x_2804_);
v___x_2806_ = lean_nat_dec_lt(v___x_2805_, v___x_2801_);
if (v___x_2806_ == 0)
{
lean_dec(v___x_2805_);
lean_dec_ref(v_block_2797_);
return v_snippet_2796_;
}
else
{
lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2850_; 
lean_inc_ref(v_declarationRange_2800_);
lean_inc_ref(v_sections_2799_);
lean_inc_ref(v_text_2798_);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_snippet_2796_);
if (v_isSharedCheck_2850_ == 0)
{
lean_object* v_unused_2851_; lean_object* v_unused_2852_; lean_object* v_unused_2853_; 
v_unused_2851_ = lean_ctor_get(v_snippet_2796_, 2);
lean_dec(v_unused_2851_);
v_unused_2852_ = lean_ctor_get(v_snippet_2796_, 1);
lean_dec(v_unused_2852_);
v_unused_2853_ = lean_ctor_get(v_snippet_2796_, 0);
lean_dec(v_unused_2853_);
v___x_2808_ = v_snippet_2796_;
v_isShared_2809_ = v_isSharedCheck_2850_;
goto v_resetjp_2807_;
}
else
{
lean_dec(v_snippet_2796_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2850_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v_v_2810_; lean_object* v_snd_2811_; lean_object* v_snd_2812_; lean_object* v_fst_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2848_; 
v_v_2810_ = lean_array_fget(v_sections_2799_, v___x_2805_);
v_snd_2811_ = lean_ctor_get(v_v_2810_, 1);
lean_inc(v_snd_2811_);
v_snd_2812_ = lean_ctor_get(v_snd_2811_, 1);
lean_inc(v_snd_2812_);
v_fst_2813_ = lean_ctor_get(v_v_2810_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_v_2810_);
if (v_isSharedCheck_2848_ == 0)
{
lean_object* v_unused_2849_; 
v_unused_2849_ = lean_ctor_get(v_v_2810_, 1);
lean_dec(v_unused_2849_);
v___x_2815_ = v_v_2810_;
v_isShared_2816_ = v_isSharedCheck_2848_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_fst_2813_);
lean_dec(v_v_2810_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2848_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_fst_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2846_; 
v_fst_2817_ = lean_ctor_get(v_snd_2811_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_snd_2811_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v_snd_2811_, 1);
lean_dec(v_unused_2847_);
v___x_2819_ = v_snd_2811_;
v_isShared_2820_ = v_isSharedCheck_2846_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_fst_2817_);
lean_dec(v_snd_2811_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2846_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v_title_2821_; lean_object* v_titleString_2822_; lean_object* v_metadata_2823_; lean_object* v_content_2824_; lean_object* v_subParts_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2845_; 
v_title_2821_ = lean_ctor_get(v_snd_2812_, 0);
v_titleString_2822_ = lean_ctor_get(v_snd_2812_, 1);
v_metadata_2823_ = lean_ctor_get(v_snd_2812_, 2);
v_content_2824_ = lean_ctor_get(v_snd_2812_, 3);
v_subParts_2825_ = lean_ctor_get(v_snd_2812_, 4);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_snd_2812_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2827_ = v_snd_2812_;
v_isShared_2828_ = v_isSharedCheck_2845_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_subParts_2825_);
lean_inc(v_content_2824_);
lean_inc(v_metadata_2823_);
lean_inc(v_titleString_2822_);
lean_inc(v_title_2821_);
lean_dec(v_snd_2812_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2845_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2829_; lean_object* v_xs_x27_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2829_ = lean_box(0);
v_xs_x27_2830_ = lean_array_fset(v_sections_2799_, v___x_2805_, v___x_2829_);
v___x_2831_ = lean_array_push(v_content_2824_, v_block_2797_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 3, v___x_2831_);
v___x_2833_ = v___x_2827_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_title_2821_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_titleString_2822_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v_metadata_2823_);
lean_ctor_set(v_reuseFailAlloc_2844_, 3, v___x_2831_);
lean_ctor_set(v_reuseFailAlloc_2844_, 4, v_subParts_2825_);
v___x_2833_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
lean_object* v___x_2835_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 1, v___x_2833_);
v___x_2835_ = v___x_2819_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_fst_2817_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v___x_2833_);
v___x_2835_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2837_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v___x_2835_);
v___x_2837_ = v___x_2815_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_fst_2813_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v___x_2835_);
v___x_2837_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2838_ = lean_array_fset(v_xs_x27_2830_, v___x_2805_, v___x_2837_);
lean_dec(v___x_2805_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 1, v___x_2838_);
v___x_2840_ = v___x_2808_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_text_2798_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2841_, 2, v_declarationRange_2800_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
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
lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2861_; 
lean_inc_ref(v_declarationRange_2800_);
lean_inc_ref(v_sections_2799_);
lean_inc_ref(v_text_2798_);
v_isSharedCheck_2861_ = !lean_is_exclusive(v_snippet_2796_);
if (v_isSharedCheck_2861_ == 0)
{
lean_object* v_unused_2862_; lean_object* v_unused_2863_; lean_object* v_unused_2864_; 
v_unused_2862_ = lean_ctor_get(v_snippet_2796_, 2);
lean_dec(v_unused_2862_);
v_unused_2863_ = lean_ctor_get(v_snippet_2796_, 1);
lean_dec(v_unused_2863_);
v_unused_2864_ = lean_ctor_get(v_snippet_2796_, 0);
lean_dec(v_unused_2864_);
v___x_2855_ = v_snippet_2796_;
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
else
{
lean_dec(v_snippet_2796_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2857_ = lean_array_push(v_text_2798_, v_block_2797_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2857_);
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_sections_2799_);
lean_ctor_set(v_reuseFailAlloc_2860_, 2, v_declarationRange_2800_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object* v_snippet_2865_, lean_object* v_level_2866_, lean_object* v_range_2867_, lean_object* v_part_2868_){
_start:
{
lean_object* v_text_2869_; lean_object* v_sections_2870_; lean_object* v_declarationRange_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2881_; 
v_text_2869_ = lean_ctor_get(v_snippet_2865_, 0);
v_sections_2870_ = lean_ctor_get(v_snippet_2865_, 1);
v_declarationRange_2871_ = lean_ctor_get(v_snippet_2865_, 2);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_snippet_2865_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2873_ = v_snippet_2865_;
v_isShared_2874_ = v_isSharedCheck_2881_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_declarationRange_2871_);
lean_inc(v_sections_2870_);
lean_inc(v_text_2869_);
lean_dec(v_snippet_2865_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2881_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2875_, 0, v_range_2867_);
lean_ctor_set(v___x_2875_, 1, v_part_2868_);
v___x_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2876_, 0, v_level_2866_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = lean_array_push(v_sections_2870_, v___x_2876_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 1, v___x_2877_);
v___x_2879_ = v___x_2873_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_text_2869_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_declarationRange_2871_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = lean_unsigned_to_nat(32u);
v___x_2883_ = lean_mk_empty_array_with_capacity(v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1(void){
_start:
{
size_t v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2885_ = ((size_t)5ULL);
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = lean_unsigned_to_nat(32u);
v___x_2888_ = lean_mk_empty_array_with_capacity(v___x_2887_);
v___x_2889_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_2890_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
lean_ctor_set(v___x_2890_, 1, v___x_2888_);
lean_ctor_set(v___x_2890_, 2, v___x_2886_);
lean_ctor_set(v___x_2890_, 3, v___x_2886_);
lean_ctor_set_usize(v___x_2890_, 4, v___x_2885_);
return v___x_2890_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default(void){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
return v___x_2891_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs(void){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_instInhabitedVersoModuleDocs_default;
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(lean_object* v_as_2893_, lean_object* v_i_2894_){
_start:
{
lean_object* v_zero_2895_; uint8_t v_isZero_2896_; 
v_zero_2895_ = lean_unsigned_to_nat(0u);
v_isZero_2896_ = lean_nat_dec_eq(v_i_2894_, v_zero_2895_);
if (v_isZero_2896_ == 1)
{
lean_object* v___x_2897_; 
lean_dec(v_i_2894_);
v___x_2897_ = lean_box(0);
return v___x_2897_;
}
else
{
lean_object* v_one_2898_; lean_object* v_n_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_one_2898_ = lean_unsigned_to_nat(1u);
v_n_2899_ = lean_nat_sub(v_i_2894_, v_one_2898_);
lean_dec(v_i_2894_);
v___x_2900_ = lean_array_fget_borrowed(v_as_2893_, v_n_2899_);
v___x_2901_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v___x_2900_);
if (lean_obj_tag(v___x_2901_) == 0)
{
v_i_2894_ = v_n_2899_;
goto _start;
}
else
{
lean_dec(v_n_2899_);
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg___boxed(lean_object* v_as_2903_, lean_object* v_i_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_2903_, v_i_2904_);
lean_dec_ref(v_as_2903_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(lean_object* v_as_2906_, lean_object* v_i_2907_){
_start:
{
lean_object* v_zero_2908_; uint8_t v_isZero_2909_; 
v_zero_2908_ = lean_unsigned_to_nat(0u);
v_isZero_2909_ = lean_nat_dec_eq(v_i_2907_, v_zero_2908_);
if (v_isZero_2909_ == 1)
{
lean_object* v___x_2910_; 
lean_dec(v_i_2907_);
v___x_2910_ = lean_box(0);
return v___x_2910_;
}
else
{
lean_object* v_one_2911_; lean_object* v_n_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v_one_2911_ = lean_unsigned_to_nat(1u);
v_n_2912_ = lean_nat_sub(v_i_2907_, v_one_2911_);
lean_dec(v_i_2907_);
v___x_2913_ = lean_array_fget_borrowed(v_as_2906_, v_n_2912_);
v___x_2914_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v___x_2913_);
if (lean_obj_tag(v___x_2914_) == 0)
{
v_i_2907_ = v_n_2912_;
goto _start;
}
else
{
lean_dec(v_n_2912_);
return v___x_2914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(lean_object* v_x_2916_){
_start:
{
if (lean_obj_tag(v_x_2916_) == 0)
{
lean_object* v_cs_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_cs_2917_ = lean_ctor_get(v_x_2916_, 0);
v___x_2918_ = lean_array_get_size(v_cs_2917_);
v___x_2919_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_cs_2917_, v___x_2918_);
return v___x_2919_;
}
else
{
lean_object* v_vs_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v_vs_2920_ = lean_ctor_get(v_x_2916_, 0);
v___x_2921_ = lean_array_get_size(v_vs_2920_);
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_vs_2920_, v___x_2921_);
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1___boxed(lean_object* v_x_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_x_2923_);
lean_dec_ref(v_x_2923_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_2925_, lean_object* v_i_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_2925_, v_i_2926_);
lean_dec_ref(v_as_2925_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(lean_object* v_t_2928_){
_start:
{
lean_object* v_root_2929_; lean_object* v_tail_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v_root_2929_ = lean_ctor_get(v_t_2928_, 0);
v_tail_2930_ = lean_ctor_get(v_t_2928_, 1);
v___x_2931_ = lean_array_get_size(v_tail_2930_);
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_tail_2930_, v___x_2931_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_root_2929_);
return v___x_2933_;
}
else
{
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0___boxed(lean_object* v_t_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_t_2934_);
lean_dec_ref(v_t_2934_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object* v_x_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting___boxed(lean_object* v_x_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_VersoModuleDocs_terminalNesting(v_x_2938_);
lean_dec_ref(v_x_2938_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(lean_object* v_as_2940_, lean_object* v_i_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_2940_, v_i_2941_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___boxed(lean_object* v_as_2944_, lean_object* v_i_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(v_as_2944_, v_i_2945_, v_a_2946_);
lean_dec_ref(v_as_2944_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(lean_object* v_as_2948_, lean_object* v_i_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_2948_, v_i_2949_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___boxed(lean_object* v_as_2952_, lean_object* v_i_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(v_as_2952_, v_i_2953_, v_a_2954_);
lean_dec_ref(v_as_2952_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object* v___x_2962_, lean_object* v_v_2963_, lean_object* v_x_2964_){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2965_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___x_2966_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2967_ = lean_box(1);
v___x_2968_ = ((lean_object*)(l_Lean_instReprVersoModuleDocs___lam__0___closed__2));
v___x_2969_ = l_Lean_PersistentArray_toArray___redArg(v_v_2963_);
v___x_2970_ = l_Array_repr___redArg(v___x_2962_, v___x_2969_);
v___x_2971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2968_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2965_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = 0;
v___x_2974_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set_uint8(v___x_2974_, sizeof(void*)*1, v___x_2973_);
lean_inc_ref(v___x_2974_);
v___x_2975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2966_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v___x_2967_);
v___x_2977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
lean_ctor_set(v___x_2977_, 1, v___x_2974_);
v___x_2978_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2977_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2965_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
lean_ctor_set_uint8(v___x_2981_, sizeof(void*)*1, v___x_2973_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object* v___x_2982_, lean_object* v_v_2983_, lean_object* v_x_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Lean_instReprVersoModuleDocs___lam__0(v___x_2982_, v_v_2983_, v_x_2984_);
lean_dec(v_x_2984_);
lean_dec_ref(v_v_2983_);
return v_res_2985_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object* v_docs_2989_){
_start:
{
uint8_t v___x_2990_; 
v___x_2990_ = l_Lean_PersistentArray_isEmpty___redArg(v_docs_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object* v_docs_2991_){
_start:
{
uint8_t v_res_2992_; lean_object* v_r_2993_; 
v_res_2992_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_2991_);
lean_dec_ref(v_docs_2991_);
v_r_2993_ = lean_box(v_res_2992_);
return v_r_2993_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object* v_docs_2994_, lean_object* v_snippet_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_2994_);
if (lean_obj_tag(v___x_2996_) == 1)
{
lean_object* v_val_2997_; uint8_t v___x_2998_; 
v_val_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_val_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___x_2998_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_2997_, v_snippet_2995_);
lean_dec(v_val_2997_);
return v___x_2998_;
}
else
{
uint8_t v___x_2999_; 
lean_dec(v___x_2996_);
v___x_2999_ = 1;
return v___x_2999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object* v_docs_3000_, lean_object* v_snippet_3001_){
_start:
{
uint8_t v_res_3002_; lean_object* v_r_3003_; 
v_res_3002_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3000_, v_snippet_3001_);
lean_dec_ref(v_snippet_3001_);
lean_dec_ref(v_docs_3000_);
v_r_3003_ = lean_box(v_res_3002_);
return v_r_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object* v_docs_3007_, lean_object* v_snippet_3008_){
_start:
{
uint8_t v___x_3009_; 
v___x_3009_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3007_, v_snippet_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; 
lean_dec_ref(v_snippet_3008_);
lean_dec_ref(v_docs_3007_);
v___x_3010_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__1));
return v___x_3010_;
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = l_Lean_PersistentArray_push___redArg(v_docs_3007_, v_snippet_3008_);
v___x_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object* v_msg_3013_){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3015_ = lean_panic_fn_borrowed(v___x_3014_, v_msg_3013_);
return v___x_3015_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_add_x21___closed__2(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3018_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__0));
v___x_3019_ = lean_unsigned_to_nat(4u);
v___x_3020_ = lean_unsigned_to_nat(291u);
v___x_3021_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__1));
v___x_3022_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__0));
v___x_3023_ = l_mkPanicMessageWithDecl(v___x_3022_, v___x_3021_, v___x_3020_, v___x_3019_, v___x_3018_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object* v_docs_3024_, lean_object* v_snippet_3025_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_3024_);
if (lean_obj_tag(v___x_3026_) == 1)
{
lean_object* v_val_3027_; uint8_t v___x_3028_; 
v_val_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_val_3027_);
lean_dec_ref_known(v___x_3026_, 1);
v___x_3028_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_3027_, v_snippet_3025_);
lean_dec(v_val_3027_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_dec_ref(v_snippet_3025_);
lean_dec_ref(v_docs_3024_);
v___x_3029_ = lean_obj_once(&l_Lean_VersoModuleDocs_add_x21___closed__2, &l_Lean_VersoModuleDocs_add_x21___closed__2_once, _init_l_Lean_VersoModuleDocs_add_x21___closed__2);
v___x_3030_ = l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(v___x_3029_);
return v___x_3030_;
}
else
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_PersistentArray_push___redArg(v_docs_3024_, v_snippet_3025_);
return v___x_3031_;
}
}
else
{
lean_object* v___x_3032_; 
lean_dec(v___x_3026_);
v___x_3032_ = l_Lean_PersistentArray_push___redArg(v_docs_3024_, v_snippet_3025_);
return v___x_3032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object* v_ctx_3033_){
_start:
{
lean_object* v_context_3034_; lean_object* v___x_3035_; 
v_context_3034_ = lean_ctor_get(v_ctx_3033_, 2);
v___x_3035_ = lean_array_get_size(v_context_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object* v_ctx_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_3036_);
lean_dec_ref(v_ctx_3036_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object* v_ctx_3041_){
_start:
{
lean_object* v_content_3042_; lean_object* v_priorParts_3043_; lean_object* v_context_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3067_; 
v_content_3042_ = lean_ctor_get(v_ctx_3041_, 0);
v_priorParts_3043_ = lean_ctor_get(v_ctx_3041_, 1);
v_context_3044_ = lean_ctor_get(v_ctx_3041_, 2);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_ctx_3041_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3046_ = v_ctx_3041_;
v_isShared_3047_ = v_isSharedCheck_3067_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_context_3044_);
lean_inc(v_priorParts_3043_);
lean_inc(v_content_3042_);
lean_dec(v_ctx_3041_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3067_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3048_ = lean_array_get_size(v_context_3044_);
v___x_3049_ = lean_unsigned_to_nat(0u);
v___x_3050_ = lean_nat_dec_eq(v___x_3048_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v_last_3053_; lean_object* v_content_3054_; lean_object* v_priorParts_3055_; lean_object* v_titleString_3056_; lean_object* v_title_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3051_ = lean_unsigned_to_nat(1u);
v___x_3052_ = lean_nat_sub(v___x_3048_, v___x_3051_);
v_last_3053_ = lean_array_fget_borrowed(v_context_3044_, v___x_3052_);
lean_dec(v___x_3052_);
v_content_3054_ = lean_ctor_get(v_last_3053_, 0);
lean_inc_ref(v_content_3054_);
v_priorParts_3055_ = lean_ctor_get(v_last_3053_, 1);
v_titleString_3056_ = lean_ctor_get(v_last_3053_, 2);
v_title_3057_ = lean_ctor_get(v_last_3053_, 3);
v___x_3058_ = lean_box(0);
lean_inc_ref(v_titleString_3056_);
lean_inc_ref(v_title_3057_);
v___x_3059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3059_, 0, v_title_3057_);
lean_ctor_set(v___x_3059_, 1, v_titleString_3056_);
lean_ctor_set(v___x_3059_, 2, v___x_3058_);
lean_ctor_set(v___x_3059_, 3, v_content_3042_);
lean_ctor_set(v___x_3059_, 4, v_priorParts_3043_);
lean_inc_ref(v_priorParts_3055_);
v___x_3060_ = lean_array_push(v_priorParts_3055_, v___x_3059_);
v___x_3061_ = lean_array_pop(v_context_3044_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 2, v___x_3061_);
lean_ctor_set(v___x_3046_, 1, v___x_3060_);
lean_ctor_set(v___x_3046_, 0, v_content_3054_);
v___x_3063_ = v___x_3046_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_content_3054_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
lean_object* v___x_3064_; 
v___x_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
return v___x_3064_;
}
}
else
{
lean_object* v___x_3066_; 
lean_del_object(v___x_3046_);
lean_dec_ref(v_context_3044_);
lean_dec_ref(v_priorParts_3043_);
lean_dec_ref(v_content_3042_);
v___x_3066_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1));
return v___x_3066_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object* v_ctx_3068_){
_start:
{
lean_object* v_context_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; 
v_context_3069_ = lean_ctor_get(v_ctx_3068_, 2);
v___x_3070_ = lean_array_get_size(v_context_3069_);
v___x_3071_ = lean_unsigned_to_nat(0u);
v___x_3072_ = lean_nat_dec_eq(v___x_3070_, v___x_3071_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; 
v___x_3073_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_3068_);
if (lean_obj_tag(v___x_3073_) == 0)
{
return v___x_3073_;
}
else
{
lean_object* v_a_3074_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref_known(v___x_3073_, 1);
v_ctx_3068_ = v_a_3074_;
goto _start;
}
}
else
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_ctx_3068_);
return v___x_3076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object* v_ctx_3079_, lean_object* v_partLevel_3080_, lean_object* v_part_3081_){
_start:
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_3079_);
v___x_3083_ = lean_nat_dec_lt(v___x_3082_, v_partLevel_3080_);
if (v___x_3083_ == 0)
{
uint8_t v___x_3084_; 
v___x_3084_ = lean_nat_dec_eq(v_partLevel_3080_, v___x_3082_);
lean_dec(v___x_3082_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; 
v___x_3085_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_3079_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_dec_ref(v_part_3081_);
lean_dec(v_partLevel_3080_);
return v___x_3085_;
}
else
{
lean_object* v_a_3086_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3085_, 1);
v_ctx_3079_ = v_a_3086_;
goto _start;
}
}
else
{
lean_object* v_content_3088_; lean_object* v_priorParts_3089_; lean_object* v_context_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_partLevel_3080_);
v_content_3088_ = lean_ctor_get(v_ctx_3079_, 0);
v_priorParts_3089_ = lean_ctor_get(v_ctx_3079_, 1);
v_context_3090_ = lean_ctor_get(v_ctx_3079_, 2);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_ctx_3079_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3092_ = v_ctx_3079_;
v_isShared_3093_ = v_isSharedCheck_3099_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_context_3090_);
lean_inc(v_priorParts_3089_);
lean_inc(v_content_3088_);
lean_dec(v_ctx_3079_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3099_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = lean_array_push(v_priorParts_3089_, v_part_3081_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v___x_3094_);
v___x_3096_ = v___x_3092_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_content_3088_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___x_3094_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_context_3090_);
v___x_3096_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
return v___x_3097_;
}
}
}
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_dec_ref(v_part_3081_);
lean_dec_ref(v_ctx_3079_);
v___x_3100_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0));
v___x_3101_ = l_Nat_reprFast(v___x_3082_);
v___x_3102_ = lean_string_append(v___x_3100_, v___x_3101_);
lean_dec_ref(v___x_3101_);
v___x_3103_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1));
v___x_3104_ = lean_string_append(v___x_3102_, v___x_3103_);
v___x_3105_ = l_Nat_reprFast(v_partLevel_3080_);
v___x_3106_ = lean_string_append(v___x_3104_, v___x_3105_);
lean_dec_ref(v___x_3105_);
v___x_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
return v___x_3107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object* v_ctx_3111_, lean_object* v_blocks_3112_){
_start:
{
lean_object* v_content_3113_; lean_object* v_priorParts_3114_; lean_object* v_context_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3128_; 
v_content_3113_ = lean_ctor_get(v_ctx_3111_, 0);
v_priorParts_3114_ = lean_ctor_get(v_ctx_3111_, 1);
v_context_3115_ = lean_ctor_get(v_ctx_3111_, 2);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_ctx_3111_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3117_ = v_ctx_3111_;
v_isShared_3118_ = v_isSharedCheck_3128_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_context_3115_);
lean_inc(v_priorParts_3114_);
lean_inc(v_content_3113_);
lean_dec(v_ctx_3111_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3128_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3119_ = lean_array_get_size(v_priorParts_3114_);
v___x_3120_ = lean_unsigned_to_nat(0u);
v___x_3121_ = lean_nat_dec_eq(v___x_3119_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
lean_del_object(v___x_3117_);
lean_dec_ref(v_context_3115_);
lean_dec_ref(v_priorParts_3114_);
lean_dec_ref(v_content_3113_);
v___x_3122_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1));
return v___x_3122_;
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3125_; 
v___x_3123_ = l_Array_append___redArg(v_content_3113_, v_blocks_3112_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v___x_3123_);
v___x_3125_ = v___x_3117_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_priorParts_3114_);
lean_ctor_set(v_reuseFailAlloc_3127_, 2, v_context_3115_);
v___x_3125_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
lean_object* v___x_3126_; 
v___x_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
return v___x_3126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object* v_ctx_3129_, lean_object* v_blocks_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_3129_, v_blocks_3130_);
lean_dec_ref(v_blocks_3130_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object* v_as_3132_, size_t v_sz_3133_, size_t v_i_3134_, lean_object* v_b_3135_){
_start:
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_usize_dec_lt(v_i_3134_, v_sz_3133_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; 
v___x_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3137_, 0, v_b_3135_);
return v___x_3137_;
}
else
{
lean_object* v_a_3138_; lean_object* v_snd_3139_; lean_object* v_fst_3140_; lean_object* v_snd_3141_; lean_object* v___x_3142_; 
v_a_3138_ = lean_array_uget_borrowed(v_as_3132_, v_i_3134_);
v_snd_3139_ = lean_ctor_get(v_a_3138_, 1);
v_fst_3140_ = lean_ctor_get(v_a_3138_, 0);
v_snd_3141_ = lean_ctor_get(v_snd_3139_, 1);
lean_inc(v_snd_3141_);
lean_inc(v_fst_3140_);
v___x_3142_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(v_b_3135_, v_fst_3140_, v_snd_3141_);
if (lean_obj_tag(v___x_3142_) == 0)
{
return v___x_3142_;
}
else
{
lean_object* v_a_3143_; size_t v___x_3144_; size_t v___x_3145_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3142_, 1);
v___x_3144_ = ((size_t)1ULL);
v___x_3145_ = lean_usize_add(v_i_3134_, v___x_3144_);
v_i_3134_ = v___x_3145_;
v_b_3135_ = v_a_3143_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object* v_as_3147_, lean_object* v_sz_3148_, lean_object* v_i_3149_, lean_object* v_b_3150_){
_start:
{
size_t v_sz_boxed_3151_; size_t v_i_boxed_3152_; lean_object* v_res_3153_; 
v_sz_boxed_3151_ = lean_unbox_usize(v_sz_3148_);
lean_dec(v_sz_3148_);
v_i_boxed_3152_ = lean_unbox_usize(v_i_3149_);
lean_dec(v_i_3149_);
v_res_3153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_3147_, v_sz_boxed_3151_, v_i_boxed_3152_, v_b_3150_);
lean_dec_ref(v_as_3147_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object* v_ctx_3154_, lean_object* v_snippet_3155_){
_start:
{
lean_object* v_text_3156_; lean_object* v_sections_3157_; lean_object* v___x_3158_; 
v_text_3156_ = lean_ctor_get(v_snippet_3155_, 0);
v_sections_3157_ = lean_ctor_get(v_snippet_3155_, 1);
v___x_3158_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_3154_, v_text_3156_);
if (lean_obj_tag(v___x_3158_) == 0)
{
return v___x_3158_;
}
else
{
lean_object* v_a_3159_; size_t v_sz_3160_; size_t v___x_3161_; lean_object* v___x_3162_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v_sz_3160_ = lean_array_size(v_sections_3157_);
v___x_3161_ = ((size_t)0ULL);
v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_sections_3157_, v_sz_3160_, v___x_3161_, v_a_3159_);
return v___x_3162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object* v_ctx_3163_, lean_object* v_snippet_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_ctx_3163_, v_snippet_3164_);
lean_dec_ref(v_snippet_3164_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object* v_as_3166_, size_t v_sz_3167_, size_t v_i_3168_, lean_object* v_b_3169_){
_start:
{
uint8_t v___x_3170_; 
v___x_3170_ = lean_usize_dec_lt(v_i_3168_, v_sz_3167_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3171_; 
v___x_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3171_, 0, v_b_3169_);
return v___x_3171_;
}
else
{
lean_object* v_snd_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3194_; 
v_snd_3172_ = lean_ctor_get(v_b_3169_, 1);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_b_3169_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; 
v_unused_3195_ = lean_ctor_get(v_b_3169_, 0);
lean_dec(v_unused_3195_);
v___x_3174_ = v_b_3169_;
v_isShared_3175_ = v_isSharedCheck_3194_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_snd_3172_);
lean_dec(v_b_3169_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3194_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v_a_3176_; lean_object* v___x_3177_; 
v_a_3176_ = lean_array_uget_borrowed(v_as_3166_, v_i_3168_);
v___x_3177_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3172_, v_a_3176_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_del_object(v___x_3174_);
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
v_a_3186_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3177_, 1);
v___x_3187_ = lean_box(0);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 1, v_a_3186_);
lean_ctor_set(v___x_3174_, 0, v___x_3187_);
v___x_3189_ = v___x_3174_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_a_3186_);
v___x_3189_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
size_t v___x_3190_; size_t v___x_3191_; 
v___x_3190_ = ((size_t)1ULL);
v___x_3191_ = lean_usize_add(v_i_3168_, v___x_3190_);
v_i_3168_ = v___x_3191_;
v_b_3169_ = v___x_3189_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3196_, lean_object* v_sz_3197_, lean_object* v_i_3198_, lean_object* v_b_3199_){
_start:
{
size_t v_sz_boxed_3200_; size_t v_i_boxed_3201_; lean_object* v_res_3202_; 
v_sz_boxed_3200_ = lean_unbox_usize(v_sz_3197_);
lean_dec(v_sz_3197_);
v_i_boxed_3201_ = lean_unbox_usize(v_i_3198_);
lean_dec(v_i_3198_);
v_res_3202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_3196_, v_sz_boxed_3200_, v_i_boxed_3201_, v_b_3199_);
lean_dec_ref(v_as_3196_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object* v_as_3203_, size_t v_sz_3204_, size_t v_i_3205_, lean_object* v_b_3206_){
_start:
{
uint8_t v___x_3207_; 
v___x_3207_ = lean_usize_dec_lt(v_i_3205_, v_sz_3204_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; 
v___x_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3208_, 0, v_b_3206_);
return v___x_3208_;
}
else
{
lean_object* v_snd_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3231_; 
v_snd_3209_ = lean_ctor_get(v_b_3206_, 1);
v_isSharedCheck_3231_ = !lean_is_exclusive(v_b_3206_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v_b_3206_, 0);
lean_dec(v_unused_3232_);
v___x_3211_ = v_b_3206_;
v_isShared_3212_ = v_isSharedCheck_3231_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_snd_3209_);
lean_dec(v_b_3206_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3231_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_a_3213_; lean_object* v___x_3214_; 
v_a_3213_ = lean_array_uget_borrowed(v_as_3203_, v_i_3205_);
v___x_3214_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3209_, v_a_3213_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_del_object(v___x_3211_);
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3214_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3214_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v_a_3223_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v___x_3214_, 1);
v___x_3224_ = lean_box(0);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 1, v_a_3223_);
lean_ctor_set(v___x_3211_, 0, v___x_3224_);
v___x_3226_ = v___x_3211_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_a_3223_);
v___x_3226_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = ((size_t)1ULL);
v___x_3228_ = lean_usize_add(v_i_3205_, v___x_3227_);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_3203_, v_sz_3204_, v___x_3228_, v___x_3226_);
return v___x_3229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object* v_as_3233_, lean_object* v_sz_3234_, lean_object* v_i_3235_, lean_object* v_b_3236_){
_start:
{
size_t v_sz_boxed_3237_; size_t v_i_boxed_3238_; lean_object* v_res_3239_; 
v_sz_boxed_3237_ = lean_unbox_usize(v_sz_3234_);
lean_dec(v_sz_3234_);
v_i_boxed_3238_ = lean_unbox_usize(v_i_3235_);
lean_dec(v_i_3235_);
v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_3233_, v_sz_boxed_3237_, v_i_boxed_3238_, v_b_3236_);
lean_dec_ref(v_as_3233_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3240_, size_t v_sz_3241_, size_t v_i_3242_, lean_object* v_b_3243_){
_start:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_usize_dec_lt(v_i_3242_, v_sz_3241_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3245_, 0, v_b_3243_);
return v___x_3245_;
}
else
{
lean_object* v_snd_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3268_; 
v_snd_3246_ = lean_ctor_get(v_b_3243_, 1);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_b_3243_);
if (v_isSharedCheck_3268_ == 0)
{
lean_object* v_unused_3269_; 
v_unused_3269_ = lean_ctor_get(v_b_3243_, 0);
lean_dec(v_unused_3269_);
v___x_3248_ = v_b_3243_;
v_isShared_3249_ = v_isSharedCheck_3268_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_snd_3246_);
lean_dec(v_b_3243_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3268_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v_a_3250_; lean_object* v___x_3251_; 
v_a_3250_ = lean_array_uget_borrowed(v_as_3240_, v_i_3242_);
v___x_3251_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3246_, v_a_3250_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_del_object(v___x_3248_);
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3261_; lean_object* v___x_3263_; 
v_a_3260_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3251_, 1);
v___x_3261_ = lean_box(0);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 1, v_a_3260_);
lean_ctor_set(v___x_3248_, 0, v___x_3261_);
v___x_3263_ = v___x_3248_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_a_3260_);
v___x_3263_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
size_t v___x_3264_; size_t v___x_3265_; 
v___x_3264_ = ((size_t)1ULL);
v___x_3265_ = lean_usize_add(v_i_3242_, v___x_3264_);
v_i_3242_ = v___x_3265_;
v_b_3243_ = v___x_3263_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3270_, lean_object* v_sz_3271_, lean_object* v_i_3272_, lean_object* v_b_3273_){
_start:
{
size_t v_sz_boxed_3274_; size_t v_i_boxed_3275_; lean_object* v_res_3276_; 
v_sz_boxed_3274_ = lean_unbox_usize(v_sz_3271_);
lean_dec(v_sz_3271_);
v_i_boxed_3275_ = lean_unbox_usize(v_i_3272_);
lean_dec(v_i_3272_);
v_res_3276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_3270_, v_sz_boxed_3274_, v_i_boxed_3275_, v_b_3273_);
lean_dec_ref(v_as_3270_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object* v_as_3277_, size_t v_sz_3278_, size_t v_i_3279_, lean_object* v_b_3280_){
_start:
{
uint8_t v___x_3281_; 
v___x_3281_ = lean_usize_dec_lt(v_i_3279_, v_sz_3278_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v_b_3280_);
return v___x_3282_;
}
else
{
lean_object* v_snd_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3305_; 
v_snd_3283_ = lean_ctor_get(v_b_3280_, 1);
v_isSharedCheck_3305_ = !lean_is_exclusive(v_b_3280_);
if (v_isSharedCheck_3305_ == 0)
{
lean_object* v_unused_3306_; 
v_unused_3306_ = lean_ctor_get(v_b_3280_, 0);
lean_dec(v_unused_3306_);
v___x_3285_ = v_b_3280_;
v_isShared_3286_ = v_isSharedCheck_3305_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_snd_3283_);
lean_dec(v_b_3280_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3305_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v_a_3287_; lean_object* v___x_3288_; 
v_a_3287_ = lean_array_uget_borrowed(v_as_3277_, v_i_3279_);
v___x_3288_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3283_, v_a_3287_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_del_object(v___x_3285_);
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
v_a_3297_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3288_, 1);
v___x_3298_ = lean_box(0);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 1, v_a_3297_);
lean_ctor_set(v___x_3285_, 0, v___x_3298_);
v___x_3300_ = v___x_3285_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3298_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_a_3297_);
v___x_3300_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
size_t v___x_3301_; size_t v___x_3302_; lean_object* v___x_3303_; 
v___x_3301_ = ((size_t)1ULL);
v___x_3302_ = lean_usize_add(v_i_3279_, v___x_3301_);
v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_3277_, v_sz_3278_, v___x_3302_, v___x_3300_);
return v___x_3303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3307_, lean_object* v_sz_3308_, lean_object* v_i_3309_, lean_object* v_b_3310_){
_start:
{
size_t v_sz_boxed_3311_; size_t v_i_boxed_3312_; lean_object* v_res_3313_; 
v_sz_boxed_3311_ = lean_unbox_usize(v_sz_3308_);
lean_dec(v_sz_3308_);
v_i_boxed_3312_ = lean_unbox_usize(v_i_3309_);
lean_dec(v_i_3309_);
v_res_3313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_3307_, v_sz_boxed_3311_, v_i_boxed_3312_, v_b_3310_);
lean_dec_ref(v_as_3307_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object* v_init_3314_, lean_object* v_n_3315_, lean_object* v_b_3316_){
_start:
{
if (lean_obj_tag(v_n_3315_) == 0)
{
lean_object* v_cs_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; size_t v_sz_3320_; size_t v___x_3321_; lean_object* v___x_3322_; 
v_cs_3317_ = lean_ctor_get(v_n_3315_, 0);
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
lean_ctor_set(v___x_3319_, 1, v_b_3316_);
v_sz_3320_ = lean_array_size(v_cs_3317_);
v___x_3321_ = ((size_t)0ULL);
v___x_3322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_3314_, v_cs_3317_, v_sz_3320_, v___x_3321_, v___x_3319_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3322_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3345_; 
v_a_3331_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3333_ = v___x_3322_;
v_isShared_3334_ = v_isSharedCheck_3345_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3322_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3345_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v_fst_3335_; 
v_fst_3335_ = lean_ctor_get(v_a_3331_, 0);
if (lean_obj_tag(v_fst_3335_) == 0)
{
lean_object* v_snd_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
v_snd_3336_ = lean_ctor_get(v_a_3331_, 1);
lean_inc(v_snd_3336_);
lean_dec(v_a_3331_);
v___x_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_snd_3336_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v___x_3337_);
v___x_3339_ = v___x_3333_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
else
{
lean_object* v_val_3341_; lean_object* v___x_3343_; 
lean_inc_ref(v_fst_3335_);
lean_dec(v_a_3331_);
v_val_3341_ = lean_ctor_get(v_fst_3335_, 0);
lean_inc(v_val_3341_);
lean_dec_ref_known(v_fst_3335_, 1);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v_val_3341_);
v___x_3343_ = v___x_3333_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_val_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
else
{
lean_object* v_vs_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; size_t v_sz_3349_; size_t v___x_3350_; lean_object* v___x_3351_; 
v_vs_3346_ = lean_ctor_get(v_n_3315_, 0);
v___x_3347_ = lean_box(0);
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
lean_ctor_set(v___x_3348_, 1, v_b_3316_);
v_sz_3349_ = lean_array_size(v_vs_3346_);
v___x_3350_ = ((size_t)0ULL);
v___x_3351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_vs_3346_, v_sz_3349_, v___x_3350_, v___x_3348_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3374_; 
v_a_3360_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3362_ = v___x_3351_;
v_isShared_3363_ = v_isSharedCheck_3374_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3351_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3374_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v_fst_3364_; 
v_fst_3364_ = lean_ctor_get(v_a_3360_, 0);
if (lean_obj_tag(v_fst_3364_) == 0)
{
lean_object* v_snd_3365_; lean_object* v___x_3366_; lean_object* v___x_3368_; 
v_snd_3365_ = lean_ctor_get(v_a_3360_, 1);
lean_inc(v_snd_3365_);
lean_dec(v_a_3360_);
v___x_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_snd_3365_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 0, v___x_3366_);
v___x_3368_ = v___x_3362_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3366_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
else
{
lean_object* v_val_3370_; lean_object* v___x_3372_; 
lean_inc_ref(v_fst_3364_);
lean_dec(v_a_3360_);
v_val_3370_ = lean_ctor_get(v_fst_3364_, 0);
lean_inc(v_val_3370_);
lean_dec_ref_known(v_fst_3364_, 1);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 0, v_val_3370_);
v___x_3372_ = v___x_3362_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_val_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object* v_init_3375_, lean_object* v_as_3376_, size_t v_sz_3377_, size_t v_i_3378_, lean_object* v_b_3379_){
_start:
{
uint8_t v___x_3380_; 
v___x_3380_ = lean_usize_dec_lt(v_i_3378_, v_sz_3377_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; 
v___x_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_b_3379_);
return v___x_3381_;
}
else
{
lean_object* v_snd_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3416_; 
v_snd_3382_ = lean_ctor_get(v_b_3379_, 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_b_3379_);
if (v_isSharedCheck_3416_ == 0)
{
lean_object* v_unused_3417_; 
v_unused_3417_ = lean_ctor_get(v_b_3379_, 0);
lean_dec(v_unused_3417_);
v___x_3384_ = v_b_3379_;
v_isShared_3385_ = v_isSharedCheck_3416_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_snd_3382_);
lean_dec(v_b_3379_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3416_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_a_3386_; lean_object* v___x_3387_; 
v_a_3386_ = lean_array_uget_borrowed(v_as_3376_, v_i_3378_);
lean_inc(v_snd_3382_);
v___x_3387_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3375_, v_a_3386_, v_snd_3382_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_del_object(v___x_3384_);
lean_dec(v_snd_3382_);
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3387_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3415_; 
v_a_3396_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3398_ = v___x_3387_;
v_isShared_3399_ = v_isSharedCheck_3415_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3387_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3415_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
if (lean_obj_tag(v_a_3396_) == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3400_, 0, v_a_3396_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3400_);
v___x_3402_ = v___x_3384_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3400_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_snd_3382_);
v___x_3402_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3404_; 
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3402_);
v___x_3404_ = v___x_3398_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3408_; lean_object* v___x_3410_; 
lean_del_object(v___x_3398_);
lean_dec(v_snd_3382_);
v_a_3407_ = lean_ctor_get(v_a_3396_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v_a_3396_, 1);
v___x_3408_ = lean_box(0);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 1, v_a_3407_);
lean_ctor_set(v___x_3384_, 0, v___x_3408_);
v___x_3410_ = v___x_3384_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_a_3407_);
v___x_3410_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
size_t v___x_3411_; size_t v___x_3412_; 
v___x_3411_ = ((size_t)1ULL);
v___x_3412_ = lean_usize_add(v_i_3378_, v___x_3411_);
v_i_3378_ = v___x_3412_;
v_b_3379_ = v___x_3410_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3418_, lean_object* v_as_3419_, lean_object* v_sz_3420_, lean_object* v_i_3421_, lean_object* v_b_3422_){
_start:
{
size_t v_sz_boxed_3423_; size_t v_i_boxed_3424_; lean_object* v_res_3425_; 
v_sz_boxed_3423_ = lean_unbox_usize(v_sz_3420_);
lean_dec(v_sz_3420_);
v_i_boxed_3424_ = lean_unbox_usize(v_i_3421_);
lean_dec(v_i_3421_);
v_res_3425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_3418_, v_as_3419_, v_sz_boxed_3423_, v_i_boxed_3424_, v_b_3422_);
lean_dec_ref(v_as_3419_);
lean_dec_ref(v_init_3418_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object* v_init_3426_, lean_object* v_n_3427_, lean_object* v_b_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3426_, v_n_3427_, v_b_3428_);
lean_dec_ref(v_n_3427_);
lean_dec_ref(v_init_3426_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object* v_t_3430_, lean_object* v_init_3431_){
_start:
{
lean_object* v_root_3432_; lean_object* v_tail_3433_; lean_object* v___x_3434_; 
v_root_3432_ = lean_ctor_get(v_t_3430_, 0);
v_tail_3433_ = lean_ctor_get(v_t_3430_, 1);
lean_inc_ref(v_init_3431_);
v___x_3434_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3431_, v_root_3432_, v_init_3431_);
lean_dec_ref(v_init_3431_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3479_; 
v_a_3443_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3445_ = v___x_3434_;
v_isShared_3446_ = v_isSharedCheck_3479_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3434_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3479_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
if (lean_obj_tag(v_a_3443_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3449_; 
v_a_3447_ = lean_ctor_get(v_a_3443_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v_a_3443_, 1);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v_a_3447_);
v___x_3449_ = v___x_3445_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; size_t v_sz_3454_; size_t v___x_3455_; lean_object* v___x_3456_; 
lean_del_object(v___x_3445_);
v_a_3451_ = lean_ctor_get(v_a_3443_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v_a_3443_, 1);
v___x_3452_ = lean_box(0);
v___x_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
lean_ctor_set(v___x_3453_, 1, v_a_3451_);
v_sz_3454_ = lean_array_size(v_tail_3433_);
v___x_3455_ = ((size_t)0ULL);
v___x_3456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_tail_3433_, v_sz_3454_, v___x_3455_, v___x_3453_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3478_; 
v_a_3465_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3467_ = v___x_3456_;
v_isShared_3468_ = v_isSharedCheck_3478_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3456_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3478_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v_fst_3469_; 
v_fst_3469_ = lean_ctor_get(v_a_3465_, 0);
if (lean_obj_tag(v_fst_3469_) == 0)
{
lean_object* v_snd_3470_; lean_object* v___x_3472_; 
v_snd_3470_ = lean_ctor_get(v_a_3465_, 1);
lean_inc(v_snd_3470_);
lean_dec(v_a_3465_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v_snd_3470_);
v___x_3472_ = v___x_3467_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_snd_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
else
{
lean_object* v_val_3474_; lean_object* v___x_3476_; 
lean_inc_ref(v_fst_3469_);
lean_dec(v_a_3465_);
v_val_3474_ = lean_ctor_get(v_fst_3469_, 0);
lean_inc(v_val_3474_);
lean_dec_ref_known(v_fst_3469_, 1);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v_val_3474_);
v___x_3476_ = v___x_3467_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_val_3474_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0___boxed(lean_object* v_t_3480_, lean_object* v_init_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_t_3480_, v_init_3481_);
lean_dec_ref(v_t_3480_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object* v_docs_3485_){
_start:
{
lean_object* v_ctx_3486_; lean_object* v___x_3487_; 
v_ctx_3486_ = ((lean_object*)(l_Lean_VersoModuleDocs_assemble___closed__0));
v___x_3487_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_docs_3485_, v_ctx_3486_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3487_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3487_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3487_, 1);
v___x_3497_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(v_a_3496_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3516_; 
v_a_3506_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3508_ = v___x_3497_;
v_isShared_3509_ = v_isSharedCheck_3516_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3497_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3516_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v_content_3510_; lean_object* v_priorParts_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
v_content_3510_ = lean_ctor_get(v_a_3506_, 0);
lean_inc_ref(v_content_3510_);
v_priorParts_3511_ = lean_ctor_get(v_a_3506_, 1);
lean_inc_ref(v_priorParts_3511_);
lean_dec(v_a_3506_);
v___x_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3512_, 0, v_content_3510_);
lean_ctor_set(v___x_3512_, 1, v_priorParts_3511_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3512_);
v___x_3514_ = v___x_3508_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble___boxed(lean_object* v_docs_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_VersoModuleDocs_assemble(v_docs_3517_);
lean_dec_ref(v_docs_3517_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_es_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = lean_array_mk(v_es_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_x_3523_, lean_object* v_x_3524_, lean_object* v_es_3525_){
_start:
{
lean_object* v_ents_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v_ents_3526_ = lean_array_mk(v_es_3525_);
v___x_3527_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
lean_inc_ref(v_ents_3526_);
v___x_3528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
lean_ctor_set(v___x_3528_, 1, v_ents_3526_);
lean_ctor_set(v___x_3528_, 2, v_ents_3526_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_x_3529_, lean_object* v_x_3530_, lean_object* v_es_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v_x_3529_, v_x_3530_, v_es_3531_);
lean_dec_ref(v_x_3530_);
lean_dec_ref(v_x_3529_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v___x_3533_, lean_object* v_x_3534_){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; size_t v___x_3538_; lean_object* v___x_3539_; 
v___x_3535_ = lean_unsigned_to_nat(32u);
v___x_3536_ = lean_mk_empty_array_with_capacity(v___x_3535_);
v___x_3537_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_3538_ = ((size_t)5ULL);
lean_inc(v___x_3533_);
v___x_3539_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3539_, 0, v___x_3537_);
lean_ctor_set(v___x_3539_, 1, v___x_3536_);
lean_ctor_set(v___x_3539_, 2, v___x_3533_);
lean_ctor_set(v___x_3539_, 3, v___x_3533_);
lean_ctor_set_usize(v___x_3539_, 4, v___x_3538_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v___x_3540_, lean_object* v_x_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v___x_3540_, v_x_3541_);
lean_dec_ref(v_x_3541_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
v___x_3564_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_a_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object* v_env_3567_){
_start:
{
lean_object* v___x_3568_; lean_object* v_toEnvExtension_3569_; lean_object* v_asyncMode_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3568_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_3569_ = lean_ctor_get(v___x_3568_, 0);
v_asyncMode_3570_ = lean_ctor_get(v_toEnvExtension_3569_, 2);
v___x_3571_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3572_ = lean_box(0);
v___x_3573_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3571_, v___x_3568_, v_env_3567_, v_asyncMode_3570_, v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object* v_env_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Lean_getMainVersoModuleDocs(v_env_3574_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_getVersoModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3576_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3577_ = lean_box(0);
v___x_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v___x_3576_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object* v_env_3579_, lean_object* v_moduleName_3580_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_Environment_getModuleIdx_x3f(v_env_3579_, v_moduleName_3580_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v___x_3582_; 
v___x_3582_ = lean_box(0);
return v___x_3582_;
}
else
{
lean_object* v_val_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3594_; 
v_val_3583_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3585_ = v___x_3581_;
v_isShared_3586_ = v_isSharedCheck_3594_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_val_3583_);
lean_dec(v___x_3581_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3594_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3587_ = lean_obj_once(&l_Lean_getVersoModuleDoc_x3f___closed__0, &l_Lean_getVersoModuleDoc_x3f___closed__0_once, _init_l_Lean_getVersoModuleDoc_x3f___closed__0);
v___x_3588_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v___x_3589_ = 1;
v___x_3590_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3587_, v___x_3588_, v_env_3579_, v_val_3583_, v___x_3589_);
lean_dec(v_val_3583_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3590_);
v___x_3592_ = v___x_3585_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object* v_env_3595_, lean_object* v_moduleName_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_getVersoModuleDoc_x3f(v_env_3595_, v_moduleName_3596_);
lean_dec(v_moduleName_3596_);
lean_dec_ref(v_env_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object* v_env_3600_, lean_object* v_snippet_3601_){
_start:
{
lean_object* v_docs_3602_; uint8_t v___x_3603_; 
lean_inc_ref(v_env_3600_);
v_docs_3602_ = l_Lean_getMainVersoModuleDocs(v_env_3600_);
v___x_3603_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3602_, v_snippet_3601_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3604_; lean_object* v___y_3606_; lean_object* v___x_3611_; 
lean_dec_ref(v_snippet_3601_);
lean_dec_ref(v_env_3600_);
v___x_3604_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__0));
v___x_3611_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_3602_);
lean_dec_ref(v_docs_3602_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v___x_3612_; 
v___x_3612_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___y_3606_ = v___x_3612_;
goto v___jp_3605_;
}
else
{
lean_object* v_val_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v_val_3613_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_val_3613_);
lean_dec_ref_known(v___x_3611_, 1);
v___x_3614_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__1));
v___x_3615_ = l_Nat_reprFast(v_val_3613_);
v___x_3616_ = lean_string_append(v___x_3614_, v___x_3615_);
lean_dec_ref(v___x_3615_);
v___x_3617_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1));
v___x_3618_ = lean_string_append(v___x_3616_, v___x_3617_);
v___y_3606_ = v___x_3618_;
goto v___jp_3605_;
}
v___jp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3607_ = lean_string_append(v___x_3604_, v___y_3606_);
lean_dec_ref(v___y_3606_);
v___x_3608_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1));
v___x_3609_ = lean_string_append(v___x_3607_, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
return v___x_3610_;
}
}
else
{
lean_object* v___x_3619_; lean_object* v_toEnvExtension_3620_; lean_object* v_asyncMode_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
lean_dec_ref(v_docs_3602_);
v___x_3619_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_3620_ = lean_ctor_get(v___x_3619_, 0);
v_asyncMode_3621_ = lean_ctor_get(v_toEnvExtension_3620_, 2);
v___x_3622_ = lean_box(0);
v___x_3623_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3619_, v_env_3600_, v_snippet_3601_, v_asyncMode_3621_, v___x_3622_);
v___x_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
return v___x_3624_;
}
}
}
lean_object* runtime_initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_doc_verso = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_doc_verso);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_doc_verso_module = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_doc_verso_module);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_docStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_docStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_versoDocStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_versoDocStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_moduleDocExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_moduleDocExt);
lean_dec_ref(res);
l_Lean_VersoModuleDocs_instInhabitedSnippet_default = _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default();
lean_mark_persistent(l_Lean_VersoModuleDocs_instInhabitedSnippet_default);
l_Lean_VersoModuleDocs_instInhabitedSnippet = _init_l_Lean_VersoModuleDocs_instInhabitedSnippet();
lean_mark_persistent(l_Lean_VersoModuleDocs_instInhabitedSnippet);
l_Lean_instInhabitedVersoModuleDocs_default = _init_l_Lean_instInhabitedVersoModuleDocs_default();
lean_mark_persistent(l_Lean_instInhabitedVersoModuleDocs_default);
l_Lean_instInhabitedVersoModuleDocs = _init_l_Lean_instInhabitedVersoModuleDocs();
lean_mark_persistent(l_Lean_instInhabitedVersoModuleDocs);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Extension(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Extension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Extension(builtin);
}
#ifdef __cplusplus
}
#endif
