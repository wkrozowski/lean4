// Lean compiler output
// Module: Lean.DocString.Extension
// Imports: public import Lean.DeclarationRange public import Lean.DocString.Markdown public import Init.Data.String.Extra import Init.Omega
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
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Std_Format_nestD(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Doc_MarkdownM_push___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object*);
lean_object* l_Lean_Doc_MarkdownM_endsWith___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Doc_MarkdownM_endBlock___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_Doc_MarkdownM_run_x27(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRange_default;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "{ name :="};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__2_value;
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "val :="};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__3 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__3_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__4 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__5 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__5_value;
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Dynamic.mk "};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__6 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__6_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__7 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__5_value),((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__7_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__8 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__8_value;
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " _ }"};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__9 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__9_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__10 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprElabInline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprElabInline___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprElabInline___closed__0 = (const lean_object*)&l_Lean_instReprElabInline___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprElabInline = (const lean_object*)&l_Lean_instReprElabInline___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__0 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__0_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__1 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__1_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__2 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__2_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__3 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__3_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__4 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__4_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__5 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__5_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__6 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__6_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__0_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__1_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__7 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__7_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__7_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__2_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__3_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__4_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__5_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__8 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__8_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__8_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__6_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__9 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__10 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__10_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__11 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__11_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__12 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__12_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__13 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__13_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__14 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__14_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__14_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__10_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__15 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__15_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__16 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__16_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__15_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__16_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__11_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__12_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__13_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__17 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__17_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__18 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__18_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__17_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__18_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__19 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__19_value;
static lean_once_cell_t l_Lean_instMarkdownInlineElabInline___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instMarkdownInlineElabInline___closed__20;
static lean_once_cell_t l_Lean_instMarkdownInlineElabInline___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instMarkdownInlineElabInline___closed__21;
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline;
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprElabBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprElabBlock___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprElabBlock___closed__0 = (const lean_object*)&l_Lean_instReprElabBlock___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprElabBlock = (const lean_object*)&l_Lean_instReprElabBlock___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0;
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock;
static const lean_array_object l_Lean_instInhabitedVersoDocString_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedVersoDocString_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedVersoDocString_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoDocString_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoDocString_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoDocString;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "doc"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "verso"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(146, 8, 133, 236, 68, 139, 240, 234)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(153, 72, 77, 160, 222, 42, 129, 126)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "whether to use Verso syntax in docstrings"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(3, 233, 138, 33, 66, 196, 218, 104)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 198, 182, 78, 108, 58, 220, 60)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_doc_verso;
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(146, 8, 133, 236, 68, 139, 240, 234)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(153, 72, 77, 160, 222, 42, 129, 126)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(237, 134, 110, 210, 89, 29, 102, 103)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "whether to use Verso syntax in module docstrings (falls back to `doc.verso` if not set)"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(3, 233, 138, 33, 66, 196, 218, 104)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 198, 182, 78, 108, 58, 220, 60)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(228, 159, 139, 71, 221, 243, 206, 45)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_doc_verso_module;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "docStringExt"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(220, 176, 252, 112, 223, 70, 141, 135)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_docStringExt;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DocString"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 151, 103, 225, 164, 122, 118, 127)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Extension"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 24, 255, 250, 40, 109, 111, 101)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(90, 73, 37, 46, 133, 14, 26, 13)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 17, 71, 28, 211, 27, 155, 40)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inheritDocStringExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 170, 221, 64, 52, 198, 31, 56)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "versoDocStringExt"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 29, 13, 95, 132, 33, 43, 178)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5;
static const lean_ctor_object l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__6 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "**"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__2 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "​"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__3 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__3_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__4 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__5 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__6 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]("};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 3, .m_data = "[ˆ^"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__9 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_findInternalDocString_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__12 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__12_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__14 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentArray_push___redArg, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moduleDocExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 198, 210, 20, 250, 243, 120, 74)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object*);
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
static lean_once_cell_t l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0;
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
static lean_once_cell_t l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4;
static lean_once_cell_t l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7_value;
static const lean_string_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9_value;
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
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4_value;
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
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_instToMarkdownSnippet___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMarkdownSnippet___lam__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instToMarkdownSnippet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMarkdownSnippet___closed__0;
static lean_once_cell_t l_Lean_instToMarkdownSnippet___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMarkdownSnippet___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet;
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoModuleDocs_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoModuleDocs;
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
static const lean_array_object l_Lean_VersoModuleDocs_assemble___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_VersoModuleDocs_assemble___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_assemble___closed__0_value;
static lean_once_cell_t l_Lean_VersoModuleDocs_assemble___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_VersoModuleDocs_assemble___closed__1;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_VersoModuleDocs_add_x21, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "versoModuleDocExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 74, 101, 232, 220, 166, 152, 230)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0(lean_object* v_v_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_name_24_; lean_object* v_val_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_51_; 
v_name_24_ = lean_ctor_get(v_v_22_, 0);
v_val_25_ = lean_ctor_get(v_v_22_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_v_22_);
if (v_isSharedCheck_51_ == 0)
{
v___x_27_ = v_v_22_;
v_isShared_28_ = v_isSharedCheck_51_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_val_25_);
lean_inc(v_name_24_);
lean_dec(v_v_22_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_51_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_29_ = lean_box(1);
v___x_30_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = l_Lean_Name_reprPrec(v_name_24_, v___x_31_);
if (v_isShared_28_ == 0)
{
lean_ctor_set_tag(v___x_27_, 5);
lean_ctor_set(v___x_27_, 1, v___x_32_);
lean_ctor_set(v___x_27_, 0, v___x_30_);
v___x_34_ = v___x_27_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___x_32_);
v___x_34_ = v_reuseFailAlloc_50_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_object* v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_35_ = l_Std_Format_nestD(v___x_34_);
v___x_36_ = 0;
v___x_37_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_37_, 0, v___x_35_);
lean_ctor_set_uint8(v___x_37_, sizeof(void*)*1, v___x_36_);
v___x_38_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_29_);
v___x_39_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_40_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_25_);
lean_dec(v_val_25_);
v___x_41_ = l_Lean_Name_reprPrec(v___x_40_, v___x_31_);
v___x_42_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_39_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_44_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = l_Std_Format_nestD(v___x_44_);
v___x_46_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set_uint8(v___x_46_, sizeof(void*)*1, v___x_36_);
v___x_47_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_38_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = l_Std_Format_nestD(v___x_47_);
v___x_49_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*1, v___x_36_);
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0___boxed(lean_object* v_v_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_instReprElabInline___lam__0(v_v_52_, v_x_53_);
lean_dec(v_x_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__0(lean_object* v_go_57_, lean_object* v_x_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_62_; 
lean_inc_ref(v___y_60_);
v___x_62_ = lean_apply_3(v_go_57_, v___y_59_, v___y_60_, v___y_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__0___boxed(lean_object* v_go_63_, lean_object* v_x_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_instMarkdownInlineElabInline___lam__0(v_go_63_, v_x_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec_ref(v___y_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__1(lean_object* v___x_69_, lean_object* v_go_70_, lean_object* v___i_71_, lean_object* v_content_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_array_get_size(v_content_72_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_nat_dec_lt(v___x_75_, v___x_76_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_dec_ref(v_content_72_);
lean_dec_ref(v_go_70_);
lean_dec_ref(v___x_69_);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___y_74_);
return v___x_79_;
}
else
{
lean_object* v___f_80_; uint8_t v___x_81_; 
v___f_80_ = lean_alloc_closure((void*)(l_Lean_instMarkdownInlineElabInline___lam__0___boxed), 5, 1);
lean_closure_set(v___f_80_, 0, v_go_70_);
v___x_81_ = lean_nat_dec_le(v___x_76_, v___x_76_);
if (v___x_81_ == 0)
{
if (v___x_78_ == 0)
{
lean_object* v___x_82_; 
lean_dec_ref(v___f_80_);
lean_dec_ref(v_content_72_);
lean_dec_ref(v___x_69_);
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_77_);
lean_ctor_set(v___x_82_, 1, v___y_74_);
return v___x_82_;
}
else
{
size_t v___x_83_; size_t v___x_84_; lean_object* v___x_499__overap_85_; lean_object* v___x_86_; 
v___x_83_ = ((size_t)0ULL);
v___x_84_ = lean_usize_of_nat(v___x_76_);
v___x_499__overap_85_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_69_, v___f_80_, v_content_72_, v___x_83_, v___x_84_, v___x_77_);
lean_inc_ref(v___y_73_);
v___x_86_ = lean_apply_2(v___x_499__overap_85_, v___y_73_, v___y_74_);
return v___x_86_;
}
}
else
{
size_t v___x_87_; size_t v___x_88_; lean_object* v___x_502__overap_89_; lean_object* v___x_90_; 
v___x_87_ = ((size_t)0ULL);
v___x_88_ = lean_usize_of_nat(v___x_76_);
v___x_502__overap_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_69_, v___f_80_, v_content_72_, v___x_87_, v___x_88_, v___x_77_);
lean_inc_ref(v___y_73_);
v___x_90_ = lean_apply_2(v___x_502__overap_89_, v___y_73_, v___y_74_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_91_, lean_object* v_go_92_, lean_object* v___i_93_, lean_object* v_content_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_instMarkdownInlineElabInline___lam__1(v___x_91_, v_go_92_, v___i_93_, v_content_94_, v___y_95_, v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec_ref(v___i_93_);
return v_res_97_;
}
}
static lean_object* _init_l_Lean_instMarkdownInlineElabInline___closed__20(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_instMarkdownInlineElabInline___closed__19));
v___x_144_ = l_ReaderT_instMonad___redArg(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_instMarkdownInlineElabInline___closed__21(void){
_start:
{
lean_object* v___x_145_; lean_object* v___f_146_; 
v___x_145_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___f_146_ = lean_alloc_closure((void*)(l_Lean_instMarkdownInlineElabInline___lam__1___boxed), 6, 1);
lean_closure_set(v___f_146_, 0, v___x_145_);
return v___f_146_;
}
}
static lean_object* _init_l_Lean_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___f_147_; 
v___f_147_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__21, &l_Lean_instMarkdownInlineElabInline___closed__21_once, _init_l_Lean_instMarkdownInlineElabInline___closed__21);
return v___f_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0(lean_object* v_v_148_, lean_object* v_x_149_){
_start:
{
lean_object* v_name_150_; lean_object* v_val_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_177_; 
v_name_150_ = lean_ctor_get(v_v_148_, 0);
v_val_151_ = lean_ctor_get(v_v_148_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_v_148_);
if (v_isSharedCheck_177_ == 0)
{
v___x_153_ = v_v_148_;
v_isShared_154_ = v_isSharedCheck_177_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_val_151_);
lean_inc(v_name_150_);
lean_dec(v_v_148_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_177_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_155_ = lean_box(1);
v___x_156_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = l_Lean_Name_reprPrec(v_name_150_, v___x_157_);
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 5);
lean_ctor_set(v___x_153_, 1, v___x_158_);
lean_ctor_set(v___x_153_, 0, v___x_156_);
v___x_160_ = v___x_153_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_158_);
v___x_160_ = v_reuseFailAlloc_176_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_161_ = l_Std_Format_nestD(v___x_160_);
v___x_162_ = 0;
v___x_163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1, v___x_162_);
v___x_164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_155_);
v___x_165_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_166_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_151_);
lean_dec(v_val_151_);
v___x_167_ = l_Lean_Name_reprPrec(v___x_166_, v___x_157_);
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_165_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = l_Std_Format_nestD(v___x_170_);
v___x_172_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*1, v___x_162_);
v___x_173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_164_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = l_Std_Format_nestD(v___x_173_);
v___x_175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*1, v___x_162_);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0___boxed(lean_object* v_v_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_instReprElabBlock___lam__0(v_v_178_, v_x_179_);
lean_dec(v_x_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_goB_183_, lean_object* v_x_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v___x_188_; 
lean_inc_ref(v___y_186_);
v___x_188_ = lean_apply_3(v_goB_183_, v___y_185_, v___y_186_, v___y_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v_goB_189_, lean_object* v_x_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0(v_goB_189_, v_x_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_195_, lean_object* v___goI_196_, lean_object* v_goB_197_, lean_object* v___b_198_, lean_object* v_content_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_array_get_size(v_content_199_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_nat_dec_lt(v___x_202_, v___x_203_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_dec_ref(v_content_199_);
lean_dec_ref(v_goB_197_);
lean_dec_ref(v___x_195_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___y_201_);
return v___x_206_;
}
else
{
lean_object* v___f_207_; uint8_t v___x_208_; 
v___f_207_ = lean_alloc_closure((void*)(l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0___boxed), 5, 1);
lean_closure_set(v___f_207_, 0, v_goB_197_);
v___x_208_ = lean_nat_dec_le(v___x_203_, v___x_203_);
if (v___x_208_ == 0)
{
if (v___x_205_ == 0)
{
lean_object* v___x_209_; 
lean_dec_ref(v___f_207_);
lean_dec_ref(v_content_199_);
lean_dec_ref(v___x_195_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_204_);
lean_ctor_set(v___x_209_, 1, v___y_201_);
return v___x_209_;
}
else
{
size_t v___x_210_; size_t v___x_211_; lean_object* v___x_499__overap_212_; lean_object* v___x_213_; 
v___x_210_ = ((size_t)0ULL);
v___x_211_ = lean_usize_of_nat(v___x_203_);
v___x_499__overap_212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_195_, v___f_207_, v_content_199_, v___x_210_, v___x_211_, v___x_204_);
lean_inc_ref(v___y_200_);
v___x_213_ = lean_apply_2(v___x_499__overap_212_, v___y_200_, v___y_201_);
return v___x_213_;
}
}
else
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_502__overap_216_; lean_object* v___x_217_; 
v___x_214_ = ((size_t)0ULL);
v___x_215_ = lean_usize_of_nat(v___x_203_);
v___x_502__overap_216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_195_, v___f_207_, v_content_199_, v___x_214_, v___x_215_, v___x_204_);
lean_inc_ref(v___y_200_);
v___x_217_ = lean_apply_2(v___x_502__overap_216_, v___y_200_, v___y_201_);
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_218_, lean_object* v___goI_219_, lean_object* v_goB_220_, lean_object* v___b_221_, lean_object* v_content_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_218_, v___goI_219_, v_goB_220_, v___b_221_, v_content_222_, v___y_223_, v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec_ref(v___b_221_);
lean_dec_ref(v___goI_219_);
return v_res_225_;
}
}
static lean_object* _init_l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0(void){
_start:
{
lean_object* v___x_226_; lean_object* v___f_227_; 
v___x_226_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___f_227_ = lean_alloc_closure((void*)(l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1___boxed), 7, 1);
lean_closure_set(v___f_227_, 0, v___x_226_);
return v___f_227_;
}
}
static lean_object* _init_l_Lean_instMarkdownBlockElabInlineElabBlock(void){
_start:
{
lean_object* v___f_228_; 
v___f_228_ = lean_obj_once(&l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0, &l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0_once, _init_l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0);
return v___f_228_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoDocString_default___closed__1(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default___closed__0));
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoDocString_default(void){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Lean_instInhabitedVersoDocString_default___closed__1, &l_Lean_instInhabitedVersoDocString_default___closed__1_once, _init_l_Lean_instInhabitedVersoDocString_default___closed__1);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoDocString(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_instInhabitedVersoDocString_default;
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object* v_name_235_, lean_object* v_decl_236_, lean_object* v_ref_237_){
_start:
{
lean_object* v_defValue_239_; lean_object* v_descr_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_267_; 
v_defValue_239_ = lean_ctor_get(v_decl_236_, 0);
v_descr_240_ = lean_ctor_get(v_decl_236_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_decl_236_);
if (v_isSharedCheck_267_ == 0)
{
v___x_242_ = v_decl_236_;
v_isShared_243_ = v_isSharedCheck_267_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_descr_240_);
lean_inc(v_defValue_239_);
lean_dec(v_decl_236_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_267_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_244_ = lean_alloc_ctor(1, 0, 1);
v___x_245_ = lean_unbox(v_defValue_239_);
lean_ctor_set_uint8(v___x_244_, 0, v___x_245_);
lean_inc(v_name_235_);
v___x_246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_246_, 0, v_name_235_);
lean_ctor_set(v___x_246_, 1, v_ref_237_);
lean_ctor_set(v___x_246_, 2, v___x_244_);
lean_ctor_set(v___x_246_, 3, v_descr_240_);
lean_inc(v_name_235_);
v___x_247_ = lean_register_option(v_name_235_, v___x_246_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_257_; 
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v___x_247_, 0);
lean_dec(v_unused_258_);
v___x_249_ = v___x_247_;
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
else
{
lean_dec(v___x_247_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_defValue_239_);
lean_ctor_set(v___x_242_, 0, v_name_235_);
v___x_252_ = v___x_242_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_name_235_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_defValue_239_);
v___x_252_ = v_reuseFailAlloc_256_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_252_);
v___x_254_ = v___x_249_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_del_object(v___x_242_);
lean_dec(v_defValue_239_);
lean_dec(v_name_235_);
v_a_259_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_247_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_247_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_268_, lean_object* v_decl_269_, lean_object* v_ref_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v_name_268_, v_decl_269_, v_ref_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_290_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_291_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_292_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_289_, v___x_290_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_312_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_313_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_314_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_311_, v___x_312_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = lean_box(1);
v___x_319_ = lean_st_mk_ref(v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v_k_325_; lean_object* v_v_326_; lean_object* v_l_327_; lean_object* v_r_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_k_325_ = lean_ctor_get(v_x_324_, 1);
v_v_326_ = lean_ctor_get(v_x_324_, 2);
v_l_327_ = lean_ctor_get(v_x_324_, 3);
v_r_328_ = lean_ctor_get(v_x_324_, 4);
v___x_329_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v_init_323_, v_l_327_);
lean_inc(v_v_326_);
lean_inc(v_k_325_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_k_325_);
lean_ctor_set(v___x_330_, 1, v_v_326_);
v___x_331_ = lean_array_push(v___x_329_, v___x_330_);
v_init_323_ = v___x_331_;
v_x_324_ = v_r_328_;
goto _start;
}
else
{
return v_init_323_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_333_, lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v_init_333_, v_x_334_);
lean_dec(v_x_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_(lean_object* v_x_338_, lean_object* v_s_339_, uint8_t v_level_340_){
_start:
{
uint8_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = 1;
v___x_342_ = l_Lean_instOrdOLeanLevel_ord(v_level_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
v___x_343_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_345_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v___x_344_, v_s_339_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed(lean_object* v_x_346_, lean_object* v_s_347_, lean_object* v_level_348_){
_start:
{
uint8_t v_level_boxed_349_; lean_object* v_res_350_; 
v_level_boxed_349_ = lean_unbox(v_level_348_);
v_res_350_ = l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_(v_x_346_, v_s_347_, v_level_boxed_349_);
lean_dec(v_s_347_);
lean_dec_ref(v_x_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___f_359_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_360_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_361_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_362_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_360_, v___x_361_, v___f_359_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed(lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_();
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0(lean_object* v_init_365_, lean_object* v_t_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v_init_365_, v_t_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_368_, lean_object* v_t_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0(v_init_368_, v_t_369_);
lean_dec(v_t_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_371_, lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
lean_object* v_k_373_; lean_object* v_v_374_; lean_object* v_l_375_; lean_object* v_r_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_k_373_ = lean_ctor_get(v_x_372_, 1);
v_v_374_ = lean_ctor_get(v_x_372_, 2);
v_l_375_ = lean_ctor_get(v_x_372_, 3);
v_r_376_ = lean_ctor_get(v_x_372_, 4);
v___x_377_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v_init_371_, v_l_375_);
lean_inc(v_v_374_);
lean_inc(v_k_373_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_k_373_);
lean_ctor_set(v___x_378_, 1, v_v_374_);
v___x_379_ = lean_array_push(v___x_377_, v___x_378_);
v_init_371_ = v___x_379_;
v_x_372_ = v_r_376_;
goto _start;
}
else
{
return v_init_371_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_381_, lean_object* v_x_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v_init_381_, v_x_382_);
lean_dec(v_x_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_(lean_object* v_x_386_, lean_object* v_s_387_, uint8_t v_level_388_){
_start:
{
uint8_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 1;
v___x_390_ = l_Lean_instOrdOLeanLevel_ord(v_level_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_393_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v___x_392_, v_s_387_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed(lean_object* v_x_394_, lean_object* v_s_395_, lean_object* v_level_396_){
_start:
{
uint8_t v_level_boxed_397_; lean_object* v_res_398_; 
v_level_boxed_397_ = lean_unbox(v_level_396_);
v_res_398_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_(v_x_394_, v_s_395_, v_level_boxed_397_);
lean_dec(v_s_395_);
lean_dec_ref(v_x_394_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___f_428_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_429_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_430_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_431_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_429_, v___x_430_, v___f_428_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed(lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_();
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0(lean_object* v_init_434_, lean_object* v_t_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v_init_434_, v_t_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_437_, lean_object* v_t_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0(v_init_437_, v_t_438_);
lean_dec(v_t_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_box(1);
v___x_442_ = lean_st_mk_ref(v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v_k_448_; lean_object* v_v_449_; lean_object* v_l_450_; lean_object* v_r_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_k_448_ = lean_ctor_get(v_x_447_, 1);
v_v_449_ = lean_ctor_get(v_x_447_, 2);
v_l_450_ = lean_ctor_get(v_x_447_, 3);
v_r_451_ = lean_ctor_get(v_x_447_, 4);
v___x_452_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v_init_446_, v_l_450_);
lean_inc(v_v_449_);
lean_inc(v_k_448_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_k_448_);
lean_ctor_set(v___x_453_, 1, v_v_449_);
v___x_454_ = lean_array_push(v___x_452_, v___x_453_);
v_init_446_ = v___x_454_;
v_x_447_ = v_r_451_;
goto _start;
}
else
{
return v_init_446_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_456_, lean_object* v_x_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v_init_456_, v_x_457_);
lean_dec(v_x_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_(lean_object* v_x_461_, lean_object* v_s_462_, uint8_t v_level_463_){
_start:
{
uint8_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 1;
v___x_465_ = l_Lean_instOrdOLeanLevel_ord(v_level_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
v___x_466_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
return v___x_466_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
v___x_468_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v___x_467_, v_s_462_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed(lean_object* v_x_469_, lean_object* v_s_470_, lean_object* v_level_471_){
_start:
{
uint8_t v_level_boxed_472_; lean_object* v_res_473_; 
v_level_boxed_472_ = lean_unbox(v_level_471_);
v_res_473_ = l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_(v_x_469_, v_s_470_, v_level_boxed_472_);
lean_dec(v_s_470_);
lean_dec_ref(v_x_469_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___f_480_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
v___x_481_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
v___x_482_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_483_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_481_, v___x_482_, v___f_480_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed(lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_();
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0(lean_object* v_init_486_, lean_object* v_t_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v_init_486_, v_t_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_489_, lean_object* v_t_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0(v_init_489_, v_t_490_);
lean_dec(v_t_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString(lean_object* v_declName_492_, lean_object* v_docString_493_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_495_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_496_ = lean_st_ref_take(v___x_495_);
v___x_497_ = l_String_removeLeadingSpaces(v_docString_493_);
v___x_498_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_492_, v___x_497_, v___x_496_);
v___x_499_ = lean_st_ref_set(v___x_495_, v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString___boxed(lean_object* v_declName_501_, lean_object* v_docString_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_addBuiltinDocString(v_declName_501_, v_docString_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object* v_k_505_, lean_object* v_t_506_){
_start:
{
if (lean_obj_tag(v_t_506_) == 0)
{
lean_object* v_k_507_; lean_object* v_v_508_; lean_object* v_l_509_; lean_object* v_r_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_1164_; 
v_k_507_ = lean_ctor_get(v_t_506_, 1);
v_v_508_ = lean_ctor_get(v_t_506_, 2);
v_l_509_ = lean_ctor_get(v_t_506_, 3);
v_r_510_ = lean_ctor_get(v_t_506_, 4);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_t_506_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v_t_506_, 0);
lean_dec(v_unused_1165_);
v___x_512_ = v_t_506_;
v_isShared_513_ = v_isSharedCheck_1164_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_r_510_);
lean_inc(v_l_509_);
lean_inc(v_v_508_);
lean_inc(v_k_507_);
lean_dec(v_t_506_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_1164_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___x_514_; 
v___x_514_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_505_, v_k_507_);
switch(v___x_514_)
{
case 0:
{
lean_object* v_impl_515_; lean_object* v___x_516_; 
v_impl_515_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_505_, v_l_509_);
v___x_516_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_515_) == 0)
{
if (lean_obj_tag(v_r_510_) == 0)
{
lean_object* v_size_517_; lean_object* v_size_518_; lean_object* v_k_519_; lean_object* v_v_520_; lean_object* v_l_521_; lean_object* v_r_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_size_517_ = lean_ctor_get(v_impl_515_, 0);
lean_inc(v_size_517_);
v_size_518_ = lean_ctor_get(v_r_510_, 0);
v_k_519_ = lean_ctor_get(v_r_510_, 1);
v_v_520_ = lean_ctor_get(v_r_510_, 2);
v_l_521_ = lean_ctor_get(v_r_510_, 3);
lean_inc(v_l_521_);
v_r_522_ = lean_ctor_get(v_r_510_, 4);
v___x_523_ = lean_unsigned_to_nat(3u);
v___x_524_ = lean_nat_mul(v___x_523_, v_size_517_);
v___x_525_ = lean_nat_dec_lt(v___x_524_, v_size_518_);
lean_dec(v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec(v_l_521_);
v___x_526_ = lean_nat_add(v___x_516_, v_size_517_);
lean_dec(v_size_517_);
v___x_527_ = lean_nat_add(v___x_526_, v_size_518_);
lean_dec(v___x_526_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 3, v_impl_515_);
lean_ctor_set(v___x_512_, 0, v___x_527_);
v___x_529_ = v___x_512_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_530_, 3, v_impl_515_);
lean_ctor_set(v_reuseFailAlloc_530_, 4, v_r_510_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
else
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_594_; 
lean_inc(v_r_522_);
lean_inc(v_v_520_);
lean_inc(v_k_519_);
lean_inc(v_size_518_);
v_isSharedCheck_594_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; lean_object* v_unused_596_; lean_object* v_unused_597_; lean_object* v_unused_598_; lean_object* v_unused_599_; 
v_unused_595_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_595_);
v_unused_596_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_596_);
v_unused_597_ = lean_ctor_get(v_r_510_, 2);
lean_dec(v_unused_597_);
v_unused_598_ = lean_ctor_get(v_r_510_, 1);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_599_);
v___x_532_ = v_r_510_;
v_isShared_533_ = v_isSharedCheck_594_;
goto v_resetjp_531_;
}
else
{
lean_dec(v_r_510_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_594_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_size_534_; lean_object* v_k_535_; lean_object* v_v_536_; lean_object* v_l_537_; lean_object* v_r_538_; lean_object* v_size_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_size_534_ = lean_ctor_get(v_l_521_, 0);
v_k_535_ = lean_ctor_get(v_l_521_, 1);
v_v_536_ = lean_ctor_get(v_l_521_, 2);
v_l_537_ = lean_ctor_get(v_l_521_, 3);
v_r_538_ = lean_ctor_get(v_l_521_, 4);
v_size_539_ = lean_ctor_get(v_r_522_, 0);
v___x_540_ = lean_unsigned_to_nat(2u);
v___x_541_ = lean_nat_mul(v___x_540_, v_size_539_);
v___x_542_ = lean_nat_dec_lt(v_size_534_, v___x_541_);
lean_dec(v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_570_; 
lean_inc(v_r_538_);
lean_inc(v_l_537_);
lean_inc(v_v_536_);
lean_inc(v_k_535_);
v_isSharedCheck_570_ = !lean_is_exclusive(v_l_521_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_571_ = lean_ctor_get(v_l_521_, 4);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_l_521_, 3);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_l_521_, 2);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_l_521_, 1);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_l_521_, 0);
lean_dec(v_unused_575_);
v___x_544_ = v_l_521_;
v_isShared_545_ = v_isSharedCheck_570_;
goto v_resetjp_543_;
}
else
{
lean_dec(v_l_521_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_570_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_560_; 
v___x_546_ = lean_nat_add(v___x_516_, v_size_517_);
lean_dec(v_size_517_);
v___x_547_ = lean_nat_add(v___x_546_, v_size_518_);
lean_dec(v_size_518_);
if (lean_obj_tag(v_l_537_) == 0)
{
lean_object* v_size_568_; 
v_size_568_ = lean_ctor_get(v_l_537_, 0);
lean_inc(v_size_568_);
v___y_560_ = v_size_568_;
goto v___jp_559_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___y_560_ = v___x_569_;
goto v___jp_559_;
}
v___jp_548_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_nat_add(v___y_549_, v___y_551_);
lean_dec(v___y_551_);
lean_dec(v___y_549_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 4, v_r_522_);
lean_ctor_set(v___x_544_, 3, v_r_538_);
lean_ctor_set(v___x_544_, 2, v_v_520_);
lean_ctor_set(v___x_544_, 1, v_k_519_);
lean_ctor_set(v___x_544_, 0, v___x_552_);
v___x_554_ = v___x_544_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_k_519_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_v_520_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_r_538_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_r_522_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 4, v___x_554_);
lean_ctor_set(v___x_532_, 3, v___y_550_);
lean_ctor_set(v___x_532_, 2, v_v_536_);
lean_ctor_set(v___x_532_, 1, v_k_535_);
lean_ctor_set(v___x_532_, 0, v___x_547_);
v___x_556_ = v___x_532_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_k_535_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_v_536_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v___y_550_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
v___jp_559_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_nat_add(v___x_546_, v___y_560_);
lean_dec(v___y_560_);
lean_dec(v___x_546_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_l_537_);
lean_ctor_set(v___x_512_, 3, v_impl_515_);
lean_ctor_set(v___x_512_, 0, v___x_561_);
v___x_563_ = v___x_512_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v_impl_515_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_l_537_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_nat_add(v___x_516_, v_size_539_);
if (lean_obj_tag(v_r_538_) == 0)
{
lean_object* v_size_565_; 
v_size_565_ = lean_ctor_get(v_r_538_, 0);
lean_inc(v_size_565_);
v___y_549_ = v___x_564_;
v___y_550_ = v___x_563_;
v___y_551_ = v_size_565_;
goto v___jp_548_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___y_549_ = v___x_564_;
v___y_550_ = v___x_563_;
v___y_551_ = v___x_566_;
goto v___jp_548_;
}
}
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
lean_del_object(v___x_512_);
v___x_576_ = lean_nat_add(v___x_516_, v_size_517_);
lean_dec(v_size_517_);
v___x_577_ = lean_nat_add(v___x_576_, v_size_518_);
lean_dec(v_size_518_);
v___x_578_ = lean_nat_add(v___x_576_, v_size_534_);
lean_dec(v___x_576_);
lean_inc_ref(v_impl_515_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 4, v_l_521_);
lean_ctor_set(v___x_532_, 3, v_impl_515_);
lean_ctor_set(v___x_532_, 2, v_v_508_);
lean_ctor_set(v___x_532_, 1, v_k_507_);
lean_ctor_set(v___x_532_, 0, v___x_578_);
v___x_580_ = v___x_532_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_impl_515_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_l_521_);
v___x_580_ = v_reuseFailAlloc_593_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v_impl_515_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; lean_object* v_unused_592_; 
v_unused_588_ = lean_ctor_get(v_impl_515_, 4);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_impl_515_, 3);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_impl_515_, 2);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_impl_515_, 1);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_impl_515_, 0);
lean_dec(v_unused_592_);
v___x_582_ = v_impl_515_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_dec(v_impl_515_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 4, v_r_522_);
lean_ctor_set(v___x_582_, 3, v___x_580_);
lean_ctor_set(v___x_582_, 2, v_v_520_);
lean_ctor_set(v___x_582_, 1, v_k_519_);
lean_ctor_set(v___x_582_, 0, v___x_577_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_k_519_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_v_520_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v_r_522_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v_size_600_ = lean_ctor_get(v_impl_515_, 0);
lean_inc(v_size_600_);
v___x_601_ = lean_nat_add(v___x_516_, v_size_600_);
lean_dec(v_size_600_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 3, v_impl_515_);
lean_ctor_set(v___x_512_, 0, v___x_601_);
v___x_603_ = v___x_512_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_impl_515_);
lean_ctor_set(v_reuseFailAlloc_604_, 4, v_r_510_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
if (lean_obj_tag(v_r_510_) == 0)
{
lean_object* v_l_605_; 
v_l_605_ = lean_ctor_get(v_r_510_, 3);
lean_inc(v_l_605_);
if (lean_obj_tag(v_l_605_) == 0)
{
lean_object* v_r_606_; 
v_r_606_ = lean_ctor_get(v_r_510_, 4);
lean_inc(v_r_606_);
if (lean_obj_tag(v_r_606_) == 0)
{
lean_object* v_size_607_; lean_object* v_k_608_; lean_object* v_v_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_622_; 
v_size_607_ = lean_ctor_get(v_r_510_, 0);
v_k_608_ = lean_ctor_get(v_r_510_, 1);
v_v_609_ = lean_ctor_get(v_r_510_, 2);
v_isSharedCheck_622_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; lean_object* v_unused_624_; 
v_unused_623_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_624_);
v___x_611_ = v_r_510_;
v_isShared_612_ = v_isSharedCheck_622_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_v_609_);
lean_inc(v_k_608_);
lean_inc(v_size_607_);
lean_dec(v_r_510_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_622_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_size_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v_size_613_ = lean_ctor_get(v_l_605_, 0);
v___x_614_ = lean_nat_add(v___x_516_, v_size_607_);
lean_dec(v_size_607_);
v___x_615_ = lean_nat_add(v___x_516_, v_size_613_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 4, v_l_605_);
lean_ctor_set(v___x_611_, 3, v_impl_515_);
lean_ctor_set(v___x_611_, 2, v_v_508_);
lean_ctor_set(v___x_611_, 1, v_k_507_);
lean_ctor_set(v___x_611_, 0, v___x_615_);
v___x_617_ = v___x_611_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_impl_515_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_l_605_);
v___x_617_ = v_reuseFailAlloc_621_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_r_606_);
lean_ctor_set(v___x_512_, 3, v___x_617_);
lean_ctor_set(v___x_512_, 2, v_v_609_);
lean_ctor_set(v___x_512_, 1, v_k_608_);
lean_ctor_set(v___x_512_, 0, v___x_614_);
v___x_619_ = v___x_512_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_k_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_v_609_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_r_606_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_k_625_; lean_object* v_v_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_649_; 
v_k_625_ = lean_ctor_get(v_r_510_, 1);
v_v_626_ = lean_ctor_get(v_r_510_, 2);
v_isSharedCheck_649_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; 
v_unused_650_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_652_);
v___x_628_ = v_r_510_;
v_isShared_629_ = v_isSharedCheck_649_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_v_626_);
lean_inc(v_k_625_);
lean_dec(v_r_510_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_649_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_k_630_; lean_object* v_v_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_645_; 
v_k_630_ = lean_ctor_get(v_l_605_, 1);
v_v_631_ = lean_ctor_get(v_l_605_, 2);
v_isSharedCheck_645_ = !lean_is_exclusive(v_l_605_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; lean_object* v_unused_647_; lean_object* v_unused_648_; 
v_unused_646_ = lean_ctor_get(v_l_605_, 4);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_l_605_, 3);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_l_605_, 0);
lean_dec(v_unused_648_);
v___x_633_ = v_l_605_;
v_isShared_634_ = v_isSharedCheck_645_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_v_631_);
lean_inc(v_k_630_);
lean_dec(v_l_605_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_645_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_unsigned_to_nat(3u);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_r_606_);
lean_ctor_set(v___x_633_, 3, v_r_606_);
lean_ctor_set(v___x_633_, 2, v_v_508_);
lean_ctor_set(v___x_633_, 1, v_k_507_);
lean_ctor_set(v___x_633_, 0, v___x_516_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_r_606_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_r_606_);
v___x_637_ = v_reuseFailAlloc_644_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 3, v_r_606_);
lean_ctor_set(v___x_628_, 0, v___x_516_);
v___x_639_ = v___x_628_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_k_625_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_v_626_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_r_606_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v_r_606_);
v___x_639_ = v_reuseFailAlloc_643_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_641_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_639_);
lean_ctor_set(v___x_512_, 3, v___x_637_);
lean_ctor_set(v___x_512_, 2, v_v_631_);
lean_ctor_set(v___x_512_, 1, v_k_630_);
lean_ctor_set(v___x_512_, 0, v___x_635_);
v___x_641_ = v___x_512_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_k_630_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_v_631_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_653_; 
v_r_653_ = lean_ctor_get(v_r_510_, 4);
lean_inc(v_r_653_);
if (lean_obj_tag(v_r_653_) == 0)
{
lean_object* v_k_654_; lean_object* v_v_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_666_; 
v_k_654_ = lean_ctor_get(v_r_510_, 1);
v_v_655_ = lean_ctor_get(v_r_510_, 2);
v_isSharedCheck_666_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; lean_object* v_unused_668_; lean_object* v_unused_669_; 
v_unused_667_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_669_);
v___x_657_ = v_r_510_;
v_isShared_658_ = v_isSharedCheck_666_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_v_655_);
lean_inc(v_k_654_);
lean_dec(v_r_510_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_666_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_unsigned_to_nat(3u);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v_l_605_);
lean_ctor_set(v___x_657_, 2, v_v_508_);
lean_ctor_set(v___x_657_, 1, v_k_507_);
lean_ctor_set(v___x_657_, 0, v___x_516_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v_l_605_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v_l_605_);
v___x_661_ = v_reuseFailAlloc_665_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_r_653_);
lean_ctor_set(v___x_512_, 3, v___x_661_);
lean_ctor_set(v___x_512_, 2, v_v_655_);
lean_ctor_set(v___x_512_, 1, v_k_654_);
lean_ctor_set(v___x_512_, 0, v___x_659_);
v___x_663_ = v___x_512_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v_r_653_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v_size_670_; lean_object* v_k_671_; lean_object* v_v_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_683_; 
v_size_670_ = lean_ctor_get(v_r_510_, 0);
v_k_671_ = lean_ctor_get(v_r_510_, 1);
v_v_672_ = lean_ctor_get(v_r_510_, 2);
v_isSharedCheck_683_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; lean_object* v_unused_685_; 
v_unused_684_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_685_);
v___x_674_ = v_r_510_;
v_isShared_675_ = v_isSharedCheck_683_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_v_672_);
lean_inc(v_k_671_);
lean_inc(v_size_670_);
lean_dec(v_r_510_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_683_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 3, v_r_653_);
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_size_670_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_r_653_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_r_653_);
v___x_677_ = v_reuseFailAlloc_682_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_unsigned_to_nat(2u);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_677_);
lean_ctor_set(v___x_512_, 3, v_r_653_);
lean_ctor_set(v___x_512_, 0, v___x_678_);
v___x_680_ = v___x_512_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_r_653_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v___x_677_);
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
}
else
{
lean_object* v___x_687_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 3, v_r_510_);
lean_ctor_set(v___x_512_, 0, v___x_516_);
v___x_687_ = v___x_512_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_r_510_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v_r_510_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
case 1:
{
lean_del_object(v___x_512_);
lean_dec(v_v_508_);
lean_dec(v_k_507_);
if (lean_obj_tag(v_l_509_) == 0)
{
if (lean_obj_tag(v_r_510_) == 0)
{
lean_object* v_size_689_; lean_object* v_k_690_; lean_object* v_v_691_; lean_object* v_l_692_; lean_object* v_r_693_; lean_object* v_size_694_; lean_object* v_k_695_; lean_object* v_v_696_; lean_object* v_l_697_; lean_object* v_r_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_size_689_ = lean_ctor_get(v_l_509_, 0);
v_k_690_ = lean_ctor_get(v_l_509_, 1);
v_v_691_ = lean_ctor_get(v_l_509_, 2);
v_l_692_ = lean_ctor_get(v_l_509_, 3);
v_r_693_ = lean_ctor_get(v_l_509_, 4);
lean_inc(v_r_693_);
v_size_694_ = lean_ctor_get(v_r_510_, 0);
v_k_695_ = lean_ctor_get(v_r_510_, 1);
v_v_696_ = lean_ctor_get(v_r_510_, 2);
v_l_697_ = lean_ctor_get(v_r_510_, 3);
lean_inc(v_l_697_);
v_r_698_ = lean_ctor_get(v_r_510_, 4);
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_nat_dec_lt(v_size_689_, v_size_694_);
if (v___x_700_ == 0)
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_836_; 
lean_inc(v_l_692_);
lean_inc(v_v_691_);
lean_inc(v_k_690_);
v_isSharedCheck_836_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; 
v_unused_837_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_841_);
v___x_702_ = v_l_509_;
v_isShared_703_ = v_isSharedCheck_836_;
goto v_resetjp_701_;
}
else
{
lean_dec(v_l_509_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_836_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v_tree_705_; 
v___x_704_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_690_, v_v_691_, v_l_692_, v_r_693_);
v_tree_705_ = lean_ctor_get(v___x_704_, 2);
lean_inc(v_tree_705_);
if (lean_obj_tag(v_tree_705_) == 0)
{
lean_object* v_k_706_; lean_object* v_v_707_; lean_object* v_size_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_k_706_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_k_706_);
v_v_707_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_v_707_);
lean_dec_ref(v___x_704_);
v_size_708_ = lean_ctor_get(v_tree_705_, 0);
v___x_709_ = lean_unsigned_to_nat(3u);
v___x_710_ = lean_nat_mul(v___x_709_, v_size_708_);
v___x_711_ = lean_nat_dec_lt(v___x_710_, v_size_694_);
lean_dec(v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
lean_dec(v_l_697_);
v___x_712_ = lean_nat_add(v___x_699_, v_size_708_);
v___x_713_ = lean_nat_add(v___x_712_, v_size_694_);
lean_dec(v___x_712_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v_r_510_);
lean_ctor_set(v___x_702_, 3, v_tree_705_);
lean_ctor_set(v___x_702_, 2, v_v_707_);
lean_ctor_set(v___x_702_, 1, v_k_706_);
lean_ctor_set(v___x_702_, 0, v___x_713_);
v___x_715_ = v___x_702_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_k_706_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_v_707_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_tree_705_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_r_510_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
else
{
lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_771_; 
lean_inc(v_r_698_);
lean_inc(v_v_696_);
lean_inc(v_k_695_);
lean_inc(v_size_694_);
v_isSharedCheck_771_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; 
v_unused_772_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_772_);
v_unused_773_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_r_510_, 2);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_r_510_, 1);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_776_);
v___x_718_ = v_r_510_;
v_isShared_719_ = v_isSharedCheck_771_;
goto v_resetjp_717_;
}
else
{
lean_dec(v_r_510_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_771_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_size_720_; lean_object* v_k_721_; lean_object* v_v_722_; lean_object* v_l_723_; lean_object* v_r_724_; lean_object* v_size_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_size_720_ = lean_ctor_get(v_l_697_, 0);
v_k_721_ = lean_ctor_get(v_l_697_, 1);
v_v_722_ = lean_ctor_get(v_l_697_, 2);
v_l_723_ = lean_ctor_get(v_l_697_, 3);
v_r_724_ = lean_ctor_get(v_l_697_, 4);
v_size_725_ = lean_ctor_get(v_r_698_, 0);
v___x_726_ = lean_unsigned_to_nat(2u);
v___x_727_ = lean_nat_mul(v___x_726_, v_size_725_);
v___x_728_ = lean_nat_dec_lt(v_size_720_, v___x_727_);
lean_dec(v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_756_; 
lean_inc(v_r_724_);
lean_inc(v_l_723_);
lean_inc(v_v_722_);
lean_inc(v_k_721_);
v_isSharedCheck_756_ = !lean_is_exclusive(v_l_697_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; lean_object* v_unused_758_; lean_object* v_unused_759_; lean_object* v_unused_760_; lean_object* v_unused_761_; 
v_unused_757_ = lean_ctor_get(v_l_697_, 4);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_l_697_, 3);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_l_697_, 2);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_l_697_, 1);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_l_697_, 0);
lean_dec(v_unused_761_);
v___x_730_ = v_l_697_;
v_isShared_731_ = v_isSharedCheck_756_;
goto v_resetjp_729_;
}
else
{
lean_dec(v_l_697_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_756_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_746_; 
v___x_732_ = lean_nat_add(v___x_699_, v_size_708_);
v___x_733_ = lean_nat_add(v___x_732_, v_size_694_);
lean_dec(v_size_694_);
if (lean_obj_tag(v_l_723_) == 0)
{
lean_object* v_size_754_; 
v_size_754_ = lean_ctor_get(v_l_723_, 0);
lean_inc(v_size_754_);
v___y_746_ = v_size_754_;
goto v___jp_745_;
}
else
{
lean_object* v___x_755_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___y_746_ = v___x_755_;
goto v___jp_745_;
}
v___jp_734_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_738_ = lean_nat_add(v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec(v___y_736_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 4, v_r_698_);
lean_ctor_set(v___x_730_, 3, v_r_724_);
lean_ctor_set(v___x_730_, 2, v_v_696_);
lean_ctor_set(v___x_730_, 1, v_k_695_);
lean_ctor_set(v___x_730_, 0, v___x_738_);
v___x_740_ = v___x_730_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v_r_724_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v_r_698_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_742_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 4, v___x_740_);
lean_ctor_set(v___x_718_, 3, v___y_735_);
lean_ctor_set(v___x_718_, 2, v_v_722_);
lean_ctor_set(v___x_718_, 1, v_k_721_);
lean_ctor_set(v___x_718_, 0, v___x_733_);
v___x_742_ = v___x_718_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_k_721_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_v_722_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v___y_735_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
v___jp_745_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = lean_nat_add(v___x_732_, v___y_746_);
lean_dec(v___y_746_);
lean_dec(v___x_732_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v_l_723_);
lean_ctor_set(v___x_702_, 3, v_tree_705_);
lean_ctor_set(v___x_702_, 2, v_v_707_);
lean_ctor_set(v___x_702_, 1, v_k_706_);
lean_ctor_set(v___x_702_, 0, v___x_747_);
v___x_749_ = v___x_702_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_k_706_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_v_707_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_tree_705_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v_l_723_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = lean_nat_add(v___x_699_, v_size_725_);
if (lean_obj_tag(v_r_724_) == 0)
{
lean_object* v_size_751_; 
v_size_751_ = lean_ctor_get(v_r_724_, 0);
lean_inc(v_size_751_);
v___y_735_ = v___x_749_;
v___y_736_ = v___x_750_;
v___y_737_ = v_size_751_;
goto v___jp_734_;
}
else
{
lean_object* v___x_752_; 
v___x_752_ = lean_unsigned_to_nat(0u);
v___y_735_ = v___x_749_;
v___y_736_ = v___x_750_;
v___y_737_ = v___x_752_;
goto v___jp_734_;
}
}
}
}
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_762_ = lean_nat_add(v___x_699_, v_size_708_);
v___x_763_ = lean_nat_add(v___x_762_, v_size_694_);
lean_dec(v_size_694_);
v___x_764_ = lean_nat_add(v___x_762_, v_size_720_);
lean_dec(v___x_762_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 4, v_l_697_);
lean_ctor_set(v___x_718_, 3, v_tree_705_);
lean_ctor_set(v___x_718_, 2, v_v_707_);
lean_ctor_set(v___x_718_, 1, v_k_706_);
lean_ctor_set(v___x_718_, 0, v___x_764_);
v___x_766_ = v___x_718_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_706_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_707_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_tree_705_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_l_697_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v_r_698_);
lean_ctor_set(v___x_702_, 3, v___x_766_);
lean_ctor_set(v___x_702_, 2, v_v_696_);
lean_ctor_set(v___x_702_, 1, v_k_695_);
lean_ctor_set(v___x_702_, 0, v___x_763_);
v___x_768_ = v___x_702_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v_r_698_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
else
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_830_; 
lean_inc(v_r_698_);
lean_inc(v_v_696_);
lean_inc(v_k_695_);
lean_inc(v_size_694_);
v_isSharedCheck_830_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; 
v_unused_831_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_r_510_, 2);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_r_510_, 1);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_835_);
v___x_778_ = v_r_510_;
v_isShared_779_ = v_isSharedCheck_830_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_r_510_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_830_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
if (lean_obj_tag(v_l_697_) == 0)
{
if (lean_obj_tag(v_r_698_) == 0)
{
lean_object* v_k_780_; lean_object* v_v_781_; lean_object* v_size_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v_k_780_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_k_780_);
v_v_781_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_v_781_);
lean_dec_ref(v___x_704_);
v_size_782_ = lean_ctor_get(v_l_697_, 0);
v___x_783_ = lean_nat_add(v___x_699_, v_size_694_);
lean_dec(v_size_694_);
v___x_784_ = lean_nat_add(v___x_699_, v_size_782_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 4, v_l_697_);
lean_ctor_set(v___x_778_, 3, v_tree_705_);
lean_ctor_set(v___x_778_, 2, v_v_781_);
lean_ctor_set(v___x_778_, 1, v_k_780_);
lean_ctor_set(v___x_778_, 0, v___x_784_);
v___x_786_ = v___x_778_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_k_780_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_v_781_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v_tree_705_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v_l_697_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v_r_698_);
lean_ctor_set(v___x_702_, 3, v___x_786_);
lean_ctor_set(v___x_702_, 2, v_v_696_);
lean_ctor_set(v___x_702_, 1, v_k_695_);
lean_ctor_set(v___x_702_, 0, v___x_783_);
v___x_788_ = v___x_702_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v_r_698_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_object* v_k_791_; lean_object* v_v_792_; lean_object* v_k_793_; lean_object* v_v_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_808_; 
lean_dec(v_size_694_);
v_k_791_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_k_791_);
v_v_792_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_v_792_);
lean_dec_ref(v___x_704_);
v_k_793_ = lean_ctor_get(v_l_697_, 1);
v_v_794_ = lean_ctor_get(v_l_697_, 2);
v_isSharedCheck_808_ = !lean_is_exclusive(v_l_697_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; lean_object* v_unused_810_; lean_object* v_unused_811_; 
v_unused_809_ = lean_ctor_get(v_l_697_, 4);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_l_697_, 3);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_l_697_, 0);
lean_dec(v_unused_811_);
v___x_796_ = v_l_697_;
v_isShared_797_ = v_isSharedCheck_808_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_v_794_);
lean_inc(v_k_793_);
lean_dec(v_l_697_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_808_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_unsigned_to_nat(3u);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 4, v_r_698_);
lean_ctor_set(v___x_796_, 3, v_r_698_);
lean_ctor_set(v___x_796_, 2, v_v_792_);
lean_ctor_set(v___x_796_, 1, v_k_791_);
lean_ctor_set(v___x_796_, 0, v___x_699_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_k_791_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_v_792_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v_r_698_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v_r_698_);
v___x_800_ = v_reuseFailAlloc_807_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 3, v_r_698_);
lean_ctor_set(v___x_778_, 0, v___x_699_);
v___x_802_ = v___x_778_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_r_698_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_r_698_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v___x_802_);
lean_ctor_set(v___x_702_, 3, v___x_800_);
lean_ctor_set(v___x_702_, 2, v_v_794_);
lean_ctor_set(v___x_702_, 1, v_k_793_);
lean_ctor_set(v___x_702_, 0, v___x_798_);
v___x_804_ = v___x_702_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_k_793_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_v_794_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_698_) == 0)
{
lean_object* v_k_812_; lean_object* v_v_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v_size_694_);
v_k_812_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_k_812_);
v_v_813_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_v_813_);
lean_dec_ref(v___x_704_);
v___x_814_ = lean_unsigned_to_nat(3u);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 4, v_l_697_);
lean_ctor_set(v___x_778_, 2, v_v_813_);
lean_ctor_set(v___x_778_, 1, v_k_812_);
lean_ctor_set(v___x_778_, 0, v___x_699_);
v___x_816_ = v___x_778_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_k_812_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_v_813_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v_l_697_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_l_697_);
v___x_816_ = v_reuseFailAlloc_820_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v_r_698_);
lean_ctor_set(v___x_702_, 3, v___x_816_);
lean_ctor_set(v___x_702_, 2, v_v_696_);
lean_ctor_set(v___x_702_, 1, v_k_695_);
lean_ctor_set(v___x_702_, 0, v___x_814_);
v___x_818_ = v___x_702_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_r_698_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v_k_821_; lean_object* v_v_822_; lean_object* v___x_824_; 
v_k_821_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_k_821_);
v_v_822_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_v_822_);
lean_dec_ref(v___x_704_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 3, v_r_698_);
v___x_824_ = v___x_778_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_size_694_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v_r_698_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v_r_698_);
v___x_824_ = v_reuseFailAlloc_829_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_unsigned_to_nat(2u);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v___x_824_);
lean_ctor_set(v___x_702_, 3, v_r_698_);
lean_ctor_set(v___x_702_, 2, v_v_822_);
lean_ctor_set(v___x_702_, 1, v_k_821_);
lean_ctor_set(v___x_702_, 0, v___x_825_);
v___x_827_ = v___x_702_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_821_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_822_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_r_698_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v___x_824_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
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
lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_994_; 
lean_inc(v_r_698_);
lean_inc(v_v_696_);
lean_inc(v_k_695_);
v_isSharedCheck_994_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; 
v_unused_995_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_r_510_, 2);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_r_510_, 1);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_999_);
v___x_843_ = v_r_510_;
v_isShared_844_ = v_isSharedCheck_994_;
goto v_resetjp_842_;
}
else
{
lean_dec(v_r_510_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_994_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v_tree_846_; 
v___x_845_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_695_, v_v_696_, v_l_697_, v_r_698_);
v_tree_846_ = lean_ctor_get(v___x_845_, 2);
lean_inc(v_tree_846_);
if (lean_obj_tag(v_tree_846_) == 0)
{
lean_object* v_k_847_; lean_object* v_v_848_; lean_object* v_size_849_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_k_847_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_k_847_);
v_v_848_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_v_848_);
lean_dec_ref(v___x_845_);
v_size_849_ = lean_ctor_get(v_tree_846_, 0);
v___x_850_ = lean_unsigned_to_nat(3u);
v___x_851_ = lean_nat_mul(v___x_850_, v_size_849_);
v___x_852_ = lean_nat_dec_lt(v___x_851_, v_size_689_);
lean_dec(v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v_r_693_);
v___x_853_ = lean_nat_add(v___x_699_, v_size_689_);
v___x_854_ = lean_nat_add(v___x_853_, v_size_849_);
lean_dec(v___x_853_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_tree_846_);
lean_ctor_set(v___x_843_, 3, v_l_509_);
lean_ctor_set(v___x_843_, 2, v_v_848_);
lean_ctor_set(v___x_843_, 1, v_k_847_);
lean_ctor_set(v___x_843_, 0, v___x_854_);
v___x_856_ = v___x_843_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_k_847_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_v_848_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_857_, 4, v_tree_846_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
else
{
lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_923_; 
lean_inc(v_l_692_);
lean_inc(v_v_691_);
lean_inc(v_k_690_);
lean_inc(v_size_689_);
v_isSharedCheck_923_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; lean_object* v_unused_925_; lean_object* v_unused_926_; lean_object* v_unused_927_; lean_object* v_unused_928_; 
v_unused_924_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_924_);
v_unused_925_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_928_);
v___x_859_ = v_l_509_;
v_isShared_860_ = v_isSharedCheck_923_;
goto v_resetjp_858_;
}
else
{
lean_dec(v_l_509_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_923_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_size_861_; lean_object* v_size_862_; lean_object* v_k_863_; lean_object* v_v_864_; lean_object* v_l_865_; lean_object* v_r_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_size_861_ = lean_ctor_get(v_l_692_, 0);
v_size_862_ = lean_ctor_get(v_r_693_, 0);
v_k_863_ = lean_ctor_get(v_r_693_, 1);
v_v_864_ = lean_ctor_get(v_r_693_, 2);
v_l_865_ = lean_ctor_get(v_r_693_, 3);
v_r_866_ = lean_ctor_get(v_r_693_, 4);
v___x_867_ = lean_unsigned_to_nat(2u);
v___x_868_ = lean_nat_mul(v___x_867_, v_size_861_);
v___x_869_ = lean_nat_dec_lt(v_size_862_, v___x_868_);
lean_dec(v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_907_; 
lean_inc(v_r_866_);
lean_inc(v_l_865_);
lean_inc(v_v_864_);
lean_inc(v_k_863_);
lean_del_object(v___x_859_);
v_isSharedCheck_907_ = !lean_is_exclusive(v_r_693_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; lean_object* v_unused_910_; lean_object* v_unused_911_; lean_object* v_unused_912_; 
v_unused_908_ = lean_ctor_get(v_r_693_, 4);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_r_693_, 3);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_r_693_, 2);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_r_693_, 1);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_r_693_, 0);
lean_dec(v_unused_912_);
v___x_871_ = v_r_693_;
v_isShared_872_ = v_isSharedCheck_907_;
goto v_resetjp_870_;
}
else
{
lean_dec(v_r_693_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_907_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___x_895_; lean_object* v___y_897_; 
v___x_873_ = lean_nat_add(v___x_699_, v_size_689_);
lean_dec(v_size_689_);
v___x_874_ = lean_nat_add(v___x_873_, v_size_849_);
lean_dec(v___x_873_);
v___x_895_ = lean_nat_add(v___x_699_, v_size_861_);
if (lean_obj_tag(v_l_865_) == 0)
{
lean_object* v_size_905_; 
v_size_905_ = lean_ctor_get(v_l_865_, 0);
lean_inc(v_size_905_);
v___y_897_ = v_size_905_;
goto v___jp_896_;
}
else
{
lean_object* v___x_906_; 
v___x_906_ = lean_unsigned_to_nat(0u);
v___y_897_ = v___x_906_;
goto v___jp_896_;
}
v___jp_875_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_nat_add(v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec(v___y_877_);
lean_inc_ref(v_tree_846_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 4, v_tree_846_);
lean_ctor_set(v___x_871_, 3, v_r_866_);
lean_ctor_set(v___x_871_, 2, v_v_848_);
lean_ctor_set(v___x_871_, 1, v_k_847_);
lean_ctor_set(v___x_871_, 0, v___x_879_);
v___x_881_ = v___x_871_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_k_847_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_v_848_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_r_866_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_tree_846_);
v___x_881_ = v_reuseFailAlloc_894_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_isSharedCheck_888_ = !lean_is_exclusive(v_tree_846_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; lean_object* v_unused_890_; lean_object* v_unused_891_; lean_object* v_unused_892_; lean_object* v_unused_893_; 
v_unused_889_ = lean_ctor_get(v_tree_846_, 4);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_tree_846_, 3);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_tree_846_, 2);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_tree_846_, 1);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_tree_846_, 0);
lean_dec(v_unused_893_);
v___x_883_ = v_tree_846_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_dec(v_tree_846_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 4, v___x_881_);
lean_ctor_set(v___x_883_, 3, v___y_876_);
lean_ctor_set(v___x_883_, 2, v_v_864_);
lean_ctor_set(v___x_883_, 1, v_k_863_);
lean_ctor_set(v___x_883_, 0, v___x_874_);
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_k_863_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_v_864_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v___y_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v___x_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
v___jp_896_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_nat_add(v___x_895_, v___y_897_);
lean_dec(v___y_897_);
lean_dec(v___x_895_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_l_865_);
lean_ctor_set(v___x_843_, 3, v_l_692_);
lean_ctor_set(v___x_843_, 2, v_v_691_);
lean_ctor_set(v___x_843_, 1, v_k_690_);
lean_ctor_set(v___x_843_, 0, v___x_898_);
v___x_900_ = v___x_843_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_k_690_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_v_691_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_l_865_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = lean_nat_add(v___x_699_, v_size_849_);
if (lean_obj_tag(v_r_866_) == 0)
{
lean_object* v_size_902_; 
v_size_902_ = lean_ctor_get(v_r_866_, 0);
lean_inc(v_size_902_);
v___y_876_ = v___x_900_;
v___y_877_ = v___x_901_;
v___y_878_ = v_size_902_;
goto v___jp_875_;
}
else
{
lean_object* v___x_903_; 
v___x_903_ = lean_unsigned_to_nat(0u);
v___y_876_ = v___x_900_;
v___y_877_ = v___x_901_;
v___y_878_ = v___x_903_;
goto v___jp_875_;
}
}
}
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_913_ = lean_nat_add(v___x_699_, v_size_689_);
lean_dec(v_size_689_);
v___x_914_ = lean_nat_add(v___x_913_, v_size_849_);
lean_dec(v___x_913_);
v___x_915_ = lean_nat_add(v___x_699_, v_size_849_);
v___x_916_ = lean_nat_add(v___x_915_, v_size_862_);
lean_dec(v___x_915_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_tree_846_);
lean_ctor_set(v___x_843_, 3, v_r_693_);
lean_ctor_set(v___x_843_, 2, v_v_848_);
lean_ctor_set(v___x_843_, 1, v_k_847_);
lean_ctor_set(v___x_843_, 0, v___x_916_);
v___x_918_ = v___x_843_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_k_847_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_v_848_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_r_693_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_tree_846_);
v___x_918_ = v_reuseFailAlloc_922_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_920_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 4, v___x_918_);
lean_ctor_set(v___x_859_, 0, v___x_914_);
v___x_920_ = v___x_859_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_690_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_v_691_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_692_) == 0)
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_952_; 
lean_inc_ref(v_l_692_);
lean_inc(v_v_691_);
lean_inc(v_k_690_);
lean_inc(v_size_689_);
v_isSharedCheck_952_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; lean_object* v_unused_957_; 
v_unused_953_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_957_);
v___x_930_ = v_l_509_;
v_isShared_931_ = v_isSharedCheck_952_;
goto v_resetjp_929_;
}
else
{
lean_dec(v_l_509_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_952_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
if (lean_obj_tag(v_r_693_) == 0)
{
lean_object* v_k_932_; lean_object* v_v_933_; lean_object* v_size_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v_k_932_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_k_932_);
v_v_933_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_v_933_);
lean_dec_ref(v___x_845_);
v_size_934_ = lean_ctor_get(v_r_693_, 0);
v___x_935_ = lean_nat_add(v___x_699_, v_size_689_);
lean_dec(v_size_689_);
v___x_936_ = lean_nat_add(v___x_699_, v_size_934_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_tree_846_);
lean_ctor_set(v___x_843_, 3, v_r_693_);
lean_ctor_set(v___x_843_, 2, v_v_933_);
lean_ctor_set(v___x_843_, 1, v_k_932_);
lean_ctor_set(v___x_843_, 0, v___x_936_);
v___x_938_ = v___x_843_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_r_693_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_tree_846_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v___x_938_);
lean_ctor_set(v___x_930_, 0, v___x_935_);
v___x_940_ = v___x_930_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_690_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_691_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
else
{
lean_object* v_k_943_; lean_object* v_v_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
lean_dec(v_size_689_);
v_k_943_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_k_943_);
v_v_944_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_v_944_);
lean_dec_ref(v___x_845_);
v___x_945_ = lean_unsigned_to_nat(3u);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_r_693_);
lean_ctor_set(v___x_843_, 3, v_r_693_);
lean_ctor_set(v___x_843_, 2, v_v_944_);
lean_ctor_set(v___x_843_, 1, v_k_943_);
lean_ctor_set(v___x_843_, 0, v___x_699_);
v___x_947_ = v___x_843_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_r_693_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_r_693_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v___x_947_);
lean_ctor_set(v___x_930_, 0, v___x_945_);
v___x_949_ = v___x_930_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_k_690_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_v_691_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_693_) == 0)
{
lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_982_; 
lean_inc(v_l_692_);
lean_inc(v_v_691_);
lean_inc(v_k_690_);
v_isSharedCheck_982_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; 
v_unused_983_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_987_);
v___x_959_ = v_l_509_;
v_isShared_960_ = v_isSharedCheck_982_;
goto v_resetjp_958_;
}
else
{
lean_dec(v_l_509_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_982_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_k_961_; lean_object* v_v_962_; lean_object* v_k_963_; lean_object* v_v_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_978_; 
v_k_961_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_k_961_);
v_v_962_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_v_962_);
lean_dec_ref(v___x_845_);
v_k_963_ = lean_ctor_get(v_r_693_, 1);
v_v_964_ = lean_ctor_get(v_r_693_, 2);
v_isSharedCheck_978_ = !lean_is_exclusive(v_r_693_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; 
v_unused_979_ = lean_ctor_get(v_r_693_, 4);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_r_693_, 3);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_r_693_, 0);
lean_dec(v_unused_981_);
v___x_966_ = v_r_693_;
v_isShared_967_ = v_isSharedCheck_978_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_v_964_);
lean_inc(v_k_963_);
lean_dec(v_r_693_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_978_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = lean_unsigned_to_nat(3u);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 4, v_l_692_);
lean_ctor_set(v___x_966_, 3, v_l_692_);
lean_ctor_set(v___x_966_, 2, v_v_691_);
lean_ctor_set(v___x_966_, 1, v_k_690_);
lean_ctor_set(v___x_966_, 0, v___x_699_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_690_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_691_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_l_692_);
v___x_970_ = v_reuseFailAlloc_977_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_l_692_);
lean_ctor_set(v___x_843_, 3, v_l_692_);
lean_ctor_set(v___x_843_, 2, v_v_962_);
lean_ctor_set(v___x_843_, 1, v_k_961_);
lean_ctor_set(v___x_843_, 0, v___x_699_);
v___x_972_ = v___x_843_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_k_961_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_v_962_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_l_692_);
v___x_972_ = v_reuseFailAlloc_976_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 4, v___x_972_);
lean_ctor_set(v___x_959_, 3, v___x_970_);
lean_ctor_set(v___x_959_, 2, v_v_964_);
lean_ctor_set(v___x_959_, 1, v_k_963_);
lean_ctor_set(v___x_959_, 0, v___x_968_);
v___x_974_ = v___x_959_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_k_963_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_v_964_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
else
{
lean_object* v_k_988_; lean_object* v_v_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v_k_988_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_k_988_);
v_v_989_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_v_989_);
lean_dec_ref(v___x_845_);
v___x_990_ = lean_unsigned_to_nat(2u);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_r_693_);
lean_ctor_set(v___x_843_, 3, v_l_509_);
lean_ctor_set(v___x_843_, 2, v_v_989_);
lean_ctor_set(v___x_843_, 1, v_k_988_);
lean_ctor_set(v___x_843_, 0, v___x_990_);
v___x_992_ = v___x_843_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_k_988_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_v_989_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_r_693_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
}
else
{
return v_l_509_;
}
}
else
{
return v_r_510_;
}
}
default: 
{
lean_object* v_impl_1000_; lean_object* v___x_1001_; 
v_impl_1000_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_505_, v_r_510_);
v___x_1001_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1000_) == 0)
{
if (lean_obj_tag(v_l_509_) == 0)
{
lean_object* v_size_1002_; lean_object* v_size_1003_; lean_object* v_k_1004_; lean_object* v_v_1005_; lean_object* v_l_1006_; lean_object* v_r_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_size_1002_ = lean_ctor_get(v_impl_1000_, 0);
lean_inc(v_size_1002_);
v_size_1003_ = lean_ctor_get(v_l_509_, 0);
v_k_1004_ = lean_ctor_get(v_l_509_, 1);
v_v_1005_ = lean_ctor_get(v_l_509_, 2);
v_l_1006_ = lean_ctor_get(v_l_509_, 3);
v_r_1007_ = lean_ctor_get(v_l_509_, 4);
lean_inc(v_r_1007_);
v___x_1008_ = lean_unsigned_to_nat(3u);
v___x_1009_ = lean_nat_mul(v___x_1008_, v_size_1002_);
v___x_1010_ = lean_nat_dec_lt(v___x_1009_, v_size_1003_);
lean_dec(v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
lean_dec(v_r_1007_);
v___x_1011_ = lean_nat_add(v___x_1001_, v_size_1003_);
v___x_1012_ = lean_nat_add(v___x_1011_, v_size_1002_);
lean_dec(v_size_1002_);
lean_dec(v___x_1011_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_impl_1000_);
lean_ctor_set(v___x_512_, 0, v___x_1012_);
v___x_1014_ = v___x_512_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_1015_, 4, v_impl_1000_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
else
{
lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1081_; 
lean_inc(v_l_1006_);
lean_inc(v_v_1005_);
lean_inc(v_k_1004_);
lean_inc(v_size_1003_);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; lean_object* v_unused_1083_; lean_object* v_unused_1084_; lean_object* v_unused_1085_; lean_object* v_unused_1086_; 
v_unused_1082_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_1084_);
v_unused_1085_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_1085_);
v_unused_1086_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_1086_);
v___x_1017_ = v_l_509_;
v_isShared_1018_ = v_isSharedCheck_1081_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v_l_509_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1081_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_size_1019_; lean_object* v_size_1020_; lean_object* v_k_1021_; lean_object* v_v_1022_; lean_object* v_l_1023_; lean_object* v_r_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v_size_1019_ = lean_ctor_get(v_l_1006_, 0);
v_size_1020_ = lean_ctor_get(v_r_1007_, 0);
v_k_1021_ = lean_ctor_get(v_r_1007_, 1);
v_v_1022_ = lean_ctor_get(v_r_1007_, 2);
v_l_1023_ = lean_ctor_get(v_r_1007_, 3);
v_r_1024_ = lean_ctor_get(v_r_1007_, 4);
v___x_1025_ = lean_unsigned_to_nat(2u);
v___x_1026_ = lean_nat_mul(v___x_1025_, v_size_1019_);
v___x_1027_ = lean_nat_dec_lt(v_size_1020_, v___x_1026_);
lean_dec(v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1056_; 
lean_inc(v_r_1024_);
lean_inc(v_l_1023_);
lean_inc(v_v_1022_);
lean_inc(v_k_1021_);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_r_1007_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; lean_object* v_unused_1058_; lean_object* v_unused_1059_; lean_object* v_unused_1060_; lean_object* v_unused_1061_; 
v_unused_1057_ = lean_ctor_get(v_r_1007_, 4);
lean_dec(v_unused_1057_);
v_unused_1058_ = lean_ctor_get(v_r_1007_, 3);
lean_dec(v_unused_1058_);
v_unused_1059_ = lean_ctor_get(v_r_1007_, 2);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_r_1007_, 1);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_r_1007_, 0);
lean_dec(v_unused_1061_);
v___x_1029_ = v_r_1007_;
v_isShared_1030_ = v_isSharedCheck_1056_;
goto v_resetjp_1028_;
}
else
{
lean_dec(v_r_1007_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1056_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___x_1044_; lean_object* v___y_1046_; 
v___x_1031_ = lean_nat_add(v___x_1001_, v_size_1003_);
lean_dec(v_size_1003_);
v___x_1032_ = lean_nat_add(v___x_1031_, v_size_1002_);
lean_dec(v___x_1031_);
v___x_1044_ = lean_nat_add(v___x_1001_, v_size_1019_);
if (lean_obj_tag(v_l_1023_) == 0)
{
lean_object* v_size_1054_; 
v_size_1054_ = lean_ctor_get(v_l_1023_, 0);
lean_inc(v_size_1054_);
v___y_1046_ = v_size_1054_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v___y_1046_ = v___x_1055_;
goto v___jp_1045_;
}
v___jp_1033_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_nat_add(v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec(v___y_1035_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 4, v_impl_1000_);
lean_ctor_set(v___x_1029_, 3, v_r_1024_);
lean_ctor_set(v___x_1029_, 2, v_v_508_);
lean_ctor_set(v___x_1029_, 1, v_k_507_);
lean_ctor_set(v___x_1029_, 0, v___x_1037_);
v___x_1039_ = v___x_1029_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_r_1024_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_impl_1000_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 4, v___x_1039_);
lean_ctor_set(v___x_1017_, 3, v___y_1034_);
lean_ctor_set(v___x_1017_, 2, v_v_1022_);
lean_ctor_set(v___x_1017_, 1, v_k_1021_);
lean_ctor_set(v___x_1017_, 0, v___x_1032_);
v___x_1041_ = v___x_1017_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_k_1021_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_v_1022_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v___y_1034_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
v___jp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = lean_nat_add(v___x_1044_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec(v___x_1044_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_l_1023_);
lean_ctor_set(v___x_512_, 3, v_l_1006_);
lean_ctor_set(v___x_512_, 2, v_v_1005_);
lean_ctor_set(v___x_512_, 1, v_k_1004_);
lean_ctor_set(v___x_512_, 0, v___x_1047_);
v___x_1049_ = v___x_512_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_l_1006_);
lean_ctor_set(v_reuseFailAlloc_1053_, 4, v_l_1023_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_nat_add(v___x_1001_, v_size_1002_);
lean_dec(v_size_1002_);
if (lean_obj_tag(v_r_1024_) == 0)
{
lean_object* v_size_1051_; 
v_size_1051_ = lean_ctor_get(v_r_1024_, 0);
lean_inc(v_size_1051_);
v___y_1034_ = v___x_1049_;
v___y_1035_ = v___x_1050_;
v___y_1036_ = v_size_1051_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_unsigned_to_nat(0u);
v___y_1034_ = v___x_1049_;
v___y_1035_ = v___x_1050_;
v___y_1036_ = v___x_1052_;
goto v___jp_1033_;
}
}
}
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_del_object(v___x_512_);
v___x_1062_ = lean_nat_add(v___x_1001_, v_size_1003_);
lean_dec(v_size_1003_);
v___x_1063_ = lean_nat_add(v___x_1062_, v_size_1002_);
lean_dec(v___x_1062_);
v___x_1064_ = lean_nat_add(v___x_1001_, v_size_1002_);
lean_dec(v_size_1002_);
v___x_1065_ = lean_nat_add(v___x_1064_, v_size_1020_);
lean_dec(v___x_1064_);
lean_inc_ref(v_impl_1000_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 4, v_impl_1000_);
lean_ctor_set(v___x_1017_, 3, v_r_1007_);
lean_ctor_set(v___x_1017_, 2, v_v_508_);
lean_ctor_set(v___x_1017_, 1, v_k_507_);
lean_ctor_set(v___x_1017_, 0, v___x_1065_);
v___x_1067_ = v___x_1017_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_r_1007_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_impl_1000_);
v___x_1067_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_isSharedCheck_1074_ = !lean_is_exclusive(v_impl_1000_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; lean_object* v_unused_1076_; lean_object* v_unused_1077_; lean_object* v_unused_1078_; lean_object* v_unused_1079_; 
v_unused_1075_ = lean_ctor_get(v_impl_1000_, 4);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_impl_1000_, 3);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_impl_1000_, 2);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_impl_1000_, 1);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v_impl_1000_, 0);
lean_dec(v_unused_1079_);
v___x_1069_ = v_impl_1000_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_dec(v_impl_1000_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 4, v___x_1067_);
lean_ctor_set(v___x_1069_, 3, v_l_1006_);
lean_ctor_set(v___x_1069_, 2, v_v_1005_);
lean_ctor_set(v___x_1069_, 1, v_k_1004_);
lean_ctor_set(v___x_1069_, 0, v___x_1063_);
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_l_1006_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v___x_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v_size_1087_ = lean_ctor_get(v_impl_1000_, 0);
lean_inc(v_size_1087_);
v___x_1088_ = lean_nat_add(v___x_1001_, v_size_1087_);
lean_dec(v_size_1087_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_impl_1000_);
lean_ctor_set(v___x_512_, 0, v___x_1088_);
v___x_1090_ = v___x_512_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_impl_1000_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
else
{
if (lean_obj_tag(v_l_509_) == 0)
{
lean_object* v_l_1092_; 
v_l_1092_ = lean_ctor_get(v_l_509_, 3);
if (lean_obj_tag(v_l_1092_) == 0)
{
lean_object* v_r_1093_; 
lean_inc_ref(v_l_1092_);
v_r_1093_ = lean_ctor_get(v_l_509_, 4);
lean_inc(v_r_1093_);
if (lean_obj_tag(v_r_1093_) == 0)
{
lean_object* v_size_1094_; lean_object* v_k_1095_; lean_object* v_v_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1109_; 
v_size_1094_ = lean_ctor_get(v_l_509_, 0);
v_k_1095_ = lean_ctor_get(v_l_509_, 1);
v_v_1096_ = lean_ctor_get(v_l_509_, 2);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; lean_object* v_unused_1111_; 
v_unused_1110_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_1111_);
v___x_1098_ = v_l_509_;
v_isShared_1099_ = v_isSharedCheck_1109_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_v_1096_);
lean_inc(v_k_1095_);
lean_inc(v_size_1094_);
lean_dec(v_l_509_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1109_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_size_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v_size_1100_ = lean_ctor_get(v_r_1093_, 0);
v___x_1101_ = lean_nat_add(v___x_1001_, v_size_1094_);
lean_dec(v_size_1094_);
v___x_1102_ = lean_nat_add(v___x_1001_, v_size_1100_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v_impl_1000_);
lean_ctor_set(v___x_1098_, 3, v_r_1093_);
lean_ctor_set(v___x_1098_, 2, v_v_508_);
lean_ctor_set(v___x_1098_, 1, v_k_507_);
lean_ctor_set(v___x_1098_, 0, v___x_1102_);
v___x_1104_ = v___x_1098_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_r_1093_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_impl_1000_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_1104_);
lean_ctor_set(v___x_512_, 3, v_l_1092_);
lean_ctor_set(v___x_512_, 2, v_v_1096_);
lean_ctor_set(v___x_512_, 1, v_k_1095_);
lean_ctor_set(v___x_512_, 0, v___x_1101_);
v___x_1106_ = v___x_512_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
else
{
lean_object* v_k_1112_; lean_object* v_v_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1124_; 
v_k_1112_ = lean_ctor_get(v_l_509_, 1);
v_v_1113_ = lean_ctor_get(v_l_509_, 2);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; lean_object* v_unused_1126_; lean_object* v_unused_1127_; 
v_unused_1125_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_1125_);
v_unused_1126_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_1127_);
v___x_1115_ = v_l_509_;
v_isShared_1116_ = v_isSharedCheck_1124_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_v_1113_);
lean_inc(v_k_1112_);
lean_dec(v_l_509_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1124_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = lean_unsigned_to_nat(3u);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 3, v_r_1093_);
lean_ctor_set(v___x_1115_, 2, v_v_508_);
lean_ctor_set(v___x_1115_, 1, v_k_507_);
lean_ctor_set(v___x_1115_, 0, v___x_1001_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_r_1093_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v_r_1093_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_1119_);
lean_ctor_set(v___x_512_, 3, v_l_1092_);
lean_ctor_set(v___x_512_, 2, v_v_1113_);
lean_ctor_set(v___x_512_, 1, v_k_1112_);
lean_ctor_set(v___x_512_, 0, v___x_1117_);
v___x_1121_ = v___x_512_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_k_1112_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_v_1113_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
else
{
lean_object* v_r_1128_; 
v_r_1128_ = lean_ctor_get(v_l_509_, 4);
lean_inc(v_r_1128_);
if (lean_obj_tag(v_r_1128_) == 0)
{
lean_object* v_k_1129_; lean_object* v_v_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1153_; 
lean_inc(v_l_1092_);
v_k_1129_ = lean_ctor_get(v_l_509_, 1);
v_v_1130_ = lean_ctor_get(v_l_509_, 2);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; lean_object* v_unused_1155_; lean_object* v_unused_1156_; 
v_unused_1154_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_1156_);
v___x_1132_ = v_l_509_;
v_isShared_1133_ = v_isSharedCheck_1153_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_v_1130_);
lean_inc(v_k_1129_);
lean_dec(v_l_509_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1153_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_k_1134_; lean_object* v_v_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1149_; 
v_k_1134_ = lean_ctor_get(v_r_1128_, 1);
v_v_1135_ = lean_ctor_get(v_r_1128_, 2);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_r_1128_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1150_ = lean_ctor_get(v_r_1128_, 4);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_r_1128_, 3);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_r_1128_, 0);
lean_dec(v_unused_1152_);
v___x_1137_ = v_r_1128_;
v_isShared_1138_ = v_isSharedCheck_1149_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_v_1135_);
lean_inc(v_k_1134_);
lean_dec(v_r_1128_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1149_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_unsigned_to_nat(3u);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 4, v_l_1092_);
lean_ctor_set(v___x_1137_, 3, v_l_1092_);
lean_ctor_set(v___x_1137_, 2, v_v_1130_);
lean_ctor_set(v___x_1137_, 1, v_k_1129_);
lean_ctor_set(v___x_1137_, 0, v___x_1001_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_k_1129_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_v_1130_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_l_1092_);
v___x_1141_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 4, v_l_1092_);
lean_ctor_set(v___x_1132_, 2, v_v_508_);
lean_ctor_set(v___x_1132_, 1, v_k_507_);
lean_ctor_set(v___x_1132_, 0, v___x_1001_);
v___x_1143_ = v___x_1132_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_l_1092_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_1143_);
lean_ctor_set(v___x_512_, 3, v___x_1141_);
lean_ctor_set(v___x_512_, 2, v_v_1135_);
lean_ctor_set(v___x_512_, 1, v_k_1134_);
lean_ctor_set(v___x_512_, 0, v___x_1139_);
v___x_1145_ = v___x_512_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_k_1134_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_v_1135_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = lean_unsigned_to_nat(2u);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_r_1128_);
lean_ctor_set(v___x_512_, 0, v___x_1157_);
v___x_1159_ = v___x_512_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v_r_1128_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v___x_1162_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_l_509_);
lean_ctor_set(v___x_512_, 0, v___x_1001_);
v___x_1162_ = v___x_512_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v_l_509_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
}
else
{
return v_t_506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg___boxed(lean_object* v_k_1166_, lean_object* v_t_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1166_, v_t_1167_);
lean_dec(v_k_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString(lean_object* v_declName_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1171_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1172_ = lean_st_ref_take(v___x_1171_);
v___x_1173_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_declName_1169_, v___x_1172_);
v___x_1174_ = lean_st_ref_set(v___x_1171_, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString___boxed(lean_object* v_declName_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_removeBuiltinDocString(v_declName_1176_);
lean_dec(v_declName_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(lean_object* v_00_u03b2_1179_, lean_object* v_k_1180_, lean_object* v_t_1181_, lean_object* v_h_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1180_, v_t_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___boxed(lean_object* v_00_u03b2_1184_, lean_object* v_k_1185_, lean_object* v_t_1186_, lean_object* v_h_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(v_00_u03b2_1184_, v_k_1185_, v_t_1186_, v_h_1187_);
lean_dec(v_k_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings(){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1191_ = lean_st_ref_get(v___x_1190_);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings___boxed(lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_getBuiltinVersoDocStrings();
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object* v_docString_1195_, lean_object* v_declName_1196_, lean_object* v_env_1197_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = l_Lean_docStringExt;
v___x_1199_ = l_String_removeLeadingSpaces(v_docString_1195_);
v___x_1200_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1198_, v_env_1197_, v_declName_1196_, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_1201_, lean_object* v___f_1202_, lean_object* v_____r_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_apply_1(v_modifyEnv_1201_, v___f_1202_);
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__0));
v___x_1207_ = l_Lean_stringToMessageData(v___x_1206_);
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__2));
v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object* v_declName_1211_, lean_object* v_modifyEnv_1212_, lean_object* v___f_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_toBind_1216_, lean_object* v___f_1217_, lean_object* v_____do__lift_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1218_, v_declName_1211_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1220_; 
lean_dec(v___f_1217_);
lean_dec(v_toBind_1216_);
lean_dec_ref(v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec(v_declName_1211_);
v___x_1220_ = lean_apply_1(v_modifyEnv_1212_, v___f_1213_);
return v___x_1220_;
}
else
{
uint8_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec_ref(v___x_1219_);
lean_dec_ref(v___f_1213_);
lean_dec(v_modifyEnv_1212_);
v___x_1221_ = 0;
v___x_1222_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1223_ = l_Lean_MessageData_ofConstName(v_declName_1211_, v___x_1221_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = l_Lean_throwError___redArg(v_inst_1214_, v_inst_1215_, v___x_1226_);
v___x_1228_ = lean_apply_4(v_toBind_1216_, lean_box(0), lean_box(0), v___x_1227_, v___f_1217_);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1229_, lean_object* v_modifyEnv_1230_, lean_object* v___f_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_toBind_1234_, lean_object* v___f_1235_, lean_object* v_____do__lift_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_addDocStringCore___redArg___lam__2(v_declName_1229_, v_modifyEnv_1230_, v___f_1231_, v_inst_1232_, v_inst_1233_, v_toBind_1234_, v___f_1235_, v_____do__lift_1236_);
lean_dec_ref(v_____do__lift_1236_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_declName_1241_, lean_object* v_docString_1242_){
_start:
{
lean_object* v_toBind_1243_; lean_object* v_getEnv_1244_; lean_object* v_modifyEnv_1245_; lean_object* v___f_1246_; lean_object* v___f_1247_; lean_object* v___f_1248_; lean_object* v___x_1249_; 
v_toBind_1243_ = lean_ctor_get(v_inst_1238_, 1);
lean_inc(v_toBind_1243_);
v_getEnv_1244_ = lean_ctor_get(v_inst_1240_, 0);
lean_inc(v_getEnv_1244_);
v_modifyEnv_1245_ = lean_ctor_get(v_inst_1240_, 1);
lean_inc(v_modifyEnv_1245_);
lean_dec_ref(v_inst_1240_);
lean_inc(v_declName_1241_);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1246_, 0, v_docString_1242_);
lean_closure_set(v___f_1246_, 1, v_declName_1241_);
lean_inc_ref(v___f_1246_);
lean_inc(v_modifyEnv_1245_);
v___f_1247_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1247_, 0, v_modifyEnv_1245_);
lean_closure_set(v___f_1247_, 1, v___f_1246_);
lean_inc(v_toBind_1243_);
v___f_1248_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1248_, 0, v_declName_1241_);
lean_closure_set(v___f_1248_, 1, v_modifyEnv_1245_);
lean_closure_set(v___f_1248_, 2, v___f_1246_);
lean_closure_set(v___f_1248_, 3, v_inst_1238_);
lean_closure_set(v___f_1248_, 4, v_inst_1239_);
lean_closure_set(v___f_1248_, 5, v_toBind_1243_);
lean_closure_set(v___f_1248_, 6, v___f_1247_);
v___x_1249_ = lean_apply_4(v_toBind_1243_, lean_box(0), lean_box(0), v_getEnv_1244_, v___f_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object* v_m_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_declName_1255_, lean_object* v_docString_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_addDocStringCore___redArg(v_inst_1251_, v_inst_1252_, v_inst_1253_, v_declName_1255_, v_docString_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object* v_m_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_declName_1263_, lean_object* v_docString_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_addDocStringCore(v_m_1258_, v_inst_1259_, v_inst_1260_, v_inst_1261_, v_inst_1262_, v_declName_1263_, v_docString_1264_);
lean_dec(v_inst_1262_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object* v_declName_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__0___closed__0));
v___x_1270_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_1269_, v_declName_1267_, v_x_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object* v___f_1271_, lean_object* v_env_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1273_ = l_Lean_docStringExt;
v___x_1274_ = lean_box(2);
v___x_1275_ = lean_box(0);
v___x_1276_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_1273_, v_env_1272_, v___f_1271_, v___x_1274_, v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__3___closed__0));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object* v_declName_1280_, lean_object* v_modifyEnv_1281_, lean_object* v___f_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_toBind_1285_, lean_object* v___f_1286_, lean_object* v_____do__lift_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1287_, v_declName_1280_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1289_; 
lean_dec(v___f_1286_);
lean_dec(v_toBind_1285_);
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
lean_dec(v_declName_1280_);
v___x_1289_ = lean_apply_1(v_modifyEnv_1281_, v___f_1282_);
return v___x_1289_;
}
else
{
uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec_ref(v___x_1288_);
lean_dec_ref(v___f_1282_);
lean_dec(v_modifyEnv_1281_);
v___x_1290_ = 0;
v___x_1291_ = lean_obj_once(&l_Lean_removeDocStringCore___redArg___lam__3___closed__1, &l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1);
v___x_1292_ = l_Lean_MessageData_ofConstName(v_declName_1280_, v___x_1290_);
v___x_1293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = l_Lean_throwError___redArg(v_inst_1283_, v_inst_1284_, v___x_1295_);
v___x_1297_ = lean_apply_4(v_toBind_1285_, lean_box(0), lean_box(0), v___x_1296_, v___f_1286_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1298_, lean_object* v_modifyEnv_1299_, lean_object* v___f_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_toBind_1303_, lean_object* v___f_1304_, lean_object* v_____do__lift_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_removeDocStringCore___redArg___lam__3(v_declName_1298_, v_modifyEnv_1299_, v___f_1300_, v_inst_1301_, v_inst_1302_, v_toBind_1303_, v___f_1304_, v_____do__lift_1305_);
lean_dec_ref(v_____do__lift_1305_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_declName_1310_){
_start:
{
lean_object* v_toBind_1311_; lean_object* v_getEnv_1312_; lean_object* v_modifyEnv_1313_; lean_object* v___f_1314_; lean_object* v___f_1315_; lean_object* v___f_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; 
v_toBind_1311_ = lean_ctor_get(v_inst_1307_, 1);
lean_inc(v_toBind_1311_);
v_getEnv_1312_ = lean_ctor_get(v_inst_1309_, 0);
lean_inc(v_getEnv_1312_);
v_modifyEnv_1313_ = lean_ctor_get(v_inst_1309_, 1);
lean_inc(v_modifyEnv_1313_);
lean_dec_ref(v_inst_1309_);
lean_inc(v_declName_1310_);
v___f_1314_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1314_, 0, v_declName_1310_);
v___f_1315_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1315_, 0, v___f_1314_);
lean_inc_ref(v___f_1315_);
lean_inc(v_modifyEnv_1313_);
v___f_1316_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1316_, 0, v_modifyEnv_1313_);
lean_closure_set(v___f_1316_, 1, v___f_1315_);
lean_inc(v_toBind_1311_);
v___f_1317_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1317_, 0, v_declName_1310_);
lean_closure_set(v___f_1317_, 1, v_modifyEnv_1313_);
lean_closure_set(v___f_1317_, 2, v___f_1315_);
lean_closure_set(v___f_1317_, 3, v_inst_1307_);
lean_closure_set(v___f_1317_, 4, v_inst_1308_);
lean_closure_set(v___f_1317_, 5, v_toBind_1311_);
lean_closure_set(v___f_1317_, 6, v___f_1316_);
v___x_1318_ = lean_apply_4(v_toBind_1311_, lean_box(0), lean_box(0), v_getEnv_1312_, v___f_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object* v_m_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_declName_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_removeDocStringCore___redArg(v_inst_1320_, v_inst_1321_, v_inst_1322_, v_declName_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object* v_m_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_declName_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_removeDocStringCore(v_m_1326_, v_inst_1327_, v_inst_1328_, v_inst_1329_, v_inst_1330_, v_declName_1331_);
lean_dec(v_inst_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_declName_1336_, lean_object* v_docString_x3f_1337_){
_start:
{
if (lean_obj_tag(v_docString_x3f_1337_) == 0)
{
lean_object* v_toApplicative_1338_; lean_object* v_toPure_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_toApplicative_1338_ = lean_ctor_get(v_inst_1333_, 0);
lean_inc_ref(v_toApplicative_1338_);
lean_dec(v_declName_1336_);
lean_dec_ref(v_inst_1335_);
lean_dec_ref(v_inst_1334_);
lean_dec_ref(v_inst_1333_);
v_toPure_1339_ = lean_ctor_get(v_toApplicative_1338_, 1);
lean_inc(v_toPure_1339_);
lean_dec_ref(v_toApplicative_1338_);
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_apply_2(v_toPure_1339_, lean_box(0), v___x_1340_);
return v___x_1341_;
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1343_; 
v_val_1342_ = lean_ctor_get(v_docString_x3f_1337_, 0);
lean_inc(v_val_1342_);
lean_dec_ref(v_docString_x3f_1337_);
v___x_1343_ = l_Lean_addDocStringCore___redArg(v_inst_1333_, v_inst_1334_, v_inst_1335_, v_declName_1336_, v_val_1342_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object* v_m_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_declName_1349_, lean_object* v_docString_x3f_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_addDocStringCore_x27___redArg(v_inst_1345_, v_inst_1346_, v_inst_1347_, v_declName_1349_, v_docString_x3f_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object* v_m_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_declName_1357_, lean_object* v_docString_x3f_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_addDocStringCore_x27(v_m_1352_, v_inst_1353_, v_inst_1354_, v_inst_1355_, v_inst_1356_, v_declName_1357_, v_docString_x3f_1358_);
lean_dec(v_inst_1356_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object* v_declName_1360_, lean_object* v_target_1361_, lean_object* v_env_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1364_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1363_, v_env_1362_, v_declName_1360_, v_target_1361_);
return v___x_1364_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__2___closed__0));
v___x_1367_ = l_Lean_stringToMessageData(v___x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object* v___x_1368_, lean_object* v_target_1369_, lean_object* v_declName_1370_, lean_object* v___x_1371_, lean_object* v_modifyEnv_1372_, lean_object* v___f_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_toBind_1376_, lean_object* v___f_1377_, lean_object* v_____do__lift_1378_){
_start:
{
lean_object* v___x_1379_; lean_object* v_toEnvExtension_1380_; lean_object* v_asyncMode_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1379_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_ref(v_toEnvExtension_1380_);
v_asyncMode_1381_ = lean_ctor_get(v_toEnvExtension_1380_, 2);
lean_inc(v_asyncMode_1381_);
lean_dec_ref(v_toEnvExtension_1380_);
v___x_1382_ = 1;
v___x_1383_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1368_, v___x_1379_, v_____do__lift_1378_, v_target_1369_, v_asyncMode_1381_, v___x_1382_);
lean_dec(v_asyncMode_1381_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_declName_1370_);
v___x_1385_ = l_Option_instBEq_beq___redArg(v___x_1371_, v___x_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
lean_dec(v___f_1377_);
lean_dec(v_toBind_1376_);
lean_dec_ref(v_inst_1375_);
lean_dec_ref(v_inst_1374_);
v___x_1386_ = lean_apply_1(v_modifyEnv_1372_, v___f_1373_);
return v___x_1386_;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v___f_1373_);
lean_dec(v_modifyEnv_1372_);
v___x_1387_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__2___closed__1, &l_Lean_addInheritedDocString___redArg___lam__2___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1);
v___x_1388_ = l_Lean_throwError___redArg(v_inst_1374_, v_inst_1375_, v___x_1387_);
v___x_1389_ = lean_apply_4(v_toBind_1376_, lean_box(0), lean_box(0), v___x_1388_, v___f_1377_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object* v_toBind_1390_, lean_object* v_getEnv_1391_, lean_object* v___f_1392_, lean_object* v_____r_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_apply_4(v_toBind_1390_, lean_box(0), lean_box(0), v_getEnv_1391_, v___f_1392_);
return v___x_1394_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__0));
v___x_1397_ = l_Lean_stringToMessageData(v___x_1396_);
return v___x_1397_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__2));
v___x_1400_ = l_Lean_stringToMessageData(v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object* v___x_1401_, lean_object* v_declName_1402_, lean_object* v_toBind_1403_, lean_object* v_getEnv_1404_, lean_object* v___f_1405_, lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v___f_1408_, lean_object* v_____do__lift_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v_toEnvExtension_1411_; lean_object* v_asyncMode_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; 
v___x_1410_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc_ref(v_toEnvExtension_1411_);
v_asyncMode_1412_ = lean_ctor_get(v_toEnvExtension_1411_, 2);
lean_inc(v_asyncMode_1412_);
lean_dec_ref(v_toEnvExtension_1411_);
v___x_1413_ = 1;
lean_inc(v_declName_1402_);
v___x_1414_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1401_, v___x_1410_, v_____do__lift_1409_, v_declName_1402_, v_asyncMode_1412_, v___x_1413_);
lean_dec(v_asyncMode_1412_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v___x_1415_; 
lean_dec(v___f_1408_);
lean_dec_ref(v_inst_1407_);
lean_dec_ref(v_inst_1406_);
lean_dec(v_declName_1402_);
v___x_1415_ = lean_apply_4(v_toBind_1403_, lean_box(0), lean_box(0), v_getEnv_1404_, v___f_1405_);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v___x_1414_);
lean_dec(v___f_1405_);
lean_dec(v_getEnv_1404_);
v___x_1416_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1417_ = 0;
v___x_1418_ = l_Lean_MessageData_ofConstName(v_declName_1402_, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1416_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__3, &l_Lean_addInheritedDocString___redArg___lam__3___closed__3_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3);
v___x_1421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v___x_1422_ = l_Lean_throwError___redArg(v_inst_1406_, v_inst_1407_, v___x_1421_);
v___x_1423_ = lean_apply_4(v_toBind_1403_, lean_box(0), lean_box(0), v___x_1422_, v___f_1408_);
return v___x_1423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object* v_declName_1424_, lean_object* v_toBind_1425_, lean_object* v_getEnv_1426_, lean_object* v___f_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v___f_1430_, lean_object* v_____do__lift_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1431_, v_declName_1424_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1433_; 
lean_dec(v___f_1430_);
lean_dec_ref(v_inst_1429_);
lean_dec_ref(v_inst_1428_);
lean_dec(v_declName_1424_);
v___x_1433_ = lean_apply_4(v_toBind_1425_, lean_box(0), lean_box(0), v_getEnv_1426_, v___f_1427_);
return v___x_1433_;
}
else
{
uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec_ref(v___x_1432_);
lean_dec(v___f_1427_);
lean_dec(v_getEnv_1426_);
v___x_1434_ = 0;
v___x_1435_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1436_ = l_Lean_MessageData_ofConstName(v_declName_1424_, v___x_1434_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = l_Lean_throwError___redArg(v_inst_1428_, v_inst_1429_, v___x_1439_);
v___x_1441_ = lean_apply_4(v_toBind_1425_, lean_box(0), lean_box(0), v___x_1440_, v___f_1430_);
return v___x_1441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object* v_declName_1442_, lean_object* v_toBind_1443_, lean_object* v_getEnv_1444_, lean_object* v___f_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v___f_1448_, lean_object* v_____do__lift_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_addInheritedDocString___redArg___lam__5(v_declName_1442_, v_toBind_1443_, v_getEnv_1444_, v___f_1445_, v_inst_1446_, v_inst_1447_, v___f_1448_, v_____do__lift_1449_);
lean_dec_ref(v_____do__lift_1449_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object* v_inst_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_declName_1455_, lean_object* v_target_1456_){
_start:
{
lean_object* v_toBind_1457_; lean_object* v_getEnv_1458_; lean_object* v_modifyEnv_1459_; lean_object* v___f_1460_; lean_object* v___f_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___f_1464_; lean_object* v___f_1465_; lean_object* v___f_1466_; lean_object* v___f_1467_; lean_object* v___f_1468_; lean_object* v___x_1469_; 
v_toBind_1457_ = lean_ctor_get(v_inst_1452_, 1);
lean_inc(v_toBind_1457_);
v_getEnv_1458_ = lean_ctor_get(v_inst_1454_, 0);
lean_inc(v_getEnv_1458_);
v_modifyEnv_1459_ = lean_ctor_get(v_inst_1454_, 1);
lean_inc(v_modifyEnv_1459_);
lean_dec_ref(v_inst_1454_);
lean_inc(v_target_1456_);
lean_inc(v_declName_1455_);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1460_, 0, v_declName_1455_);
lean_closure_set(v___f_1460_, 1, v_target_1456_);
lean_inc_ref(v___f_1460_);
lean_inc(v_modifyEnv_1459_);
v___f_1461_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1461_, 0, v_modifyEnv_1459_);
lean_closure_set(v___f_1461_, 1, v___f_1460_);
v___x_1462_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___closed__0));
v___x_1463_ = lean_box(0);
lean_inc(v_toBind_1457_);
lean_inc_ref(v_inst_1453_);
lean_inc_ref(v_inst_1452_);
lean_inc(v_declName_1455_);
v___f_1464_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__2), 11, 10);
lean_closure_set(v___f_1464_, 0, v___x_1463_);
lean_closure_set(v___f_1464_, 1, v_target_1456_);
lean_closure_set(v___f_1464_, 2, v_declName_1455_);
lean_closure_set(v___f_1464_, 3, v___x_1462_);
lean_closure_set(v___f_1464_, 4, v_modifyEnv_1459_);
lean_closure_set(v___f_1464_, 5, v___f_1460_);
lean_closure_set(v___f_1464_, 6, v_inst_1452_);
lean_closure_set(v___f_1464_, 7, v_inst_1453_);
lean_closure_set(v___f_1464_, 8, v_toBind_1457_);
lean_closure_set(v___f_1464_, 9, v___f_1461_);
lean_inc_ref(v___f_1464_);
lean_inc(v_getEnv_1458_);
lean_inc(v_toBind_1457_);
v___f_1465_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1465_, 0, v_toBind_1457_);
lean_closure_set(v___f_1465_, 1, v_getEnv_1458_);
lean_closure_set(v___f_1465_, 2, v___f_1464_);
lean_inc_ref(v_inst_1453_);
lean_inc_ref(v_inst_1452_);
lean_inc(v_getEnv_1458_);
lean_inc(v_toBind_1457_);
lean_inc(v_declName_1455_);
v___f_1466_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__3), 9, 8);
lean_closure_set(v___f_1466_, 0, v___x_1463_);
lean_closure_set(v___f_1466_, 1, v_declName_1455_);
lean_closure_set(v___f_1466_, 2, v_toBind_1457_);
lean_closure_set(v___f_1466_, 3, v_getEnv_1458_);
lean_closure_set(v___f_1466_, 4, v___f_1464_);
lean_closure_set(v___f_1466_, 5, v_inst_1452_);
lean_closure_set(v___f_1466_, 6, v_inst_1453_);
lean_closure_set(v___f_1466_, 7, v___f_1465_);
lean_inc_ref(v___f_1466_);
lean_inc(v_getEnv_1458_);
lean_inc(v_toBind_1457_);
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1467_, 0, v_toBind_1457_);
lean_closure_set(v___f_1467_, 1, v_getEnv_1458_);
lean_closure_set(v___f_1467_, 2, v___f_1466_);
lean_inc(v_getEnv_1458_);
lean_inc(v_toBind_1457_);
v___f_1468_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1468_, 0, v_declName_1455_);
lean_closure_set(v___f_1468_, 1, v_toBind_1457_);
lean_closure_set(v___f_1468_, 2, v_getEnv_1458_);
lean_closure_set(v___f_1468_, 3, v___f_1466_);
lean_closure_set(v___f_1468_, 4, v_inst_1452_);
lean_closure_set(v___f_1468_, 5, v_inst_1453_);
lean_closure_set(v___f_1468_, 6, v___f_1467_);
v___x_1469_ = lean_apply_4(v_toBind_1457_, lean_box(0), lean_box(0), v_getEnv_1458_, v___f_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object* v_m_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_, lean_object* v_inst_1473_, lean_object* v_declName_1474_, lean_object* v_target_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_addInheritedDocString___redArg(v_inst_1471_, v_inst_1472_, v_inst_1473_, v_declName_1474_, v_target_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object* v_env_1478_, lean_object* v_declName_1479_, uint8_t v_includeBuiltin_1480_){
_start:
{
lean_object* v___x_1485_; lean_object* v_toEnvExtension_1486_; lean_object* v_asyncMode_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1485_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc_ref(v_toEnvExtension_1486_);
v_asyncMode_1487_ = lean_ctor_get(v_toEnvExtension_1486_, 2);
lean_inc(v_asyncMode_1487_);
lean_dec_ref(v_toEnvExtension_1486_);
v___x_1488_ = lean_box(0);
v___x_1489_ = 1;
lean_inc(v_declName_1479_);
lean_inc_ref(v_env_1478_);
v___x_1490_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1488_, v___x_1485_, v_env_1478_, v_declName_1479_, v_asyncMode_1487_, v___x_1489_);
lean_dec(v_asyncMode_1487_);
if (lean_obj_tag(v___x_1490_) == 1)
{
lean_object* v_val_1491_; 
lean_dec(v_declName_1479_);
v_val_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_val_1491_);
lean_dec_ref(v___x_1490_);
v_declName_1479_ = v_val_1491_;
goto _start;
}
else
{
lean_object* v___x_1493_; lean_object* v_toEnvExtension_1494_; lean_object* v_asyncMode_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_dec(v___x_1490_);
v___x_1493_ = l_Lean_docStringExt;
v_toEnvExtension_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc_ref(v_toEnvExtension_1494_);
v_asyncMode_1495_ = lean_ctor_get(v_toEnvExtension_1494_, 2);
lean_inc(v_asyncMode_1495_);
lean_dec_ref(v_toEnvExtension_1494_);
v___x_1496_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
lean_inc(v_declName_1479_);
lean_inc_ref(v_env_1478_);
v___x_1497_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1496_, v___x_1493_, v_env_1478_, v_declName_1479_, v_asyncMode_1495_, v___x_1489_);
lean_dec(v_asyncMode_1495_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; lean_object* v_toEnvExtension_1499_; lean_object* v_asyncMode_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1498_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc_ref(v_toEnvExtension_1499_);
v_asyncMode_1500_ = lean_ctor_get(v_toEnvExtension_1499_, 2);
lean_inc(v_asyncMode_1500_);
lean_dec_ref(v_toEnvExtension_1499_);
v___x_1501_ = l_Lean_instInhabitedVersoDocString_default;
lean_inc(v_declName_1479_);
v___x_1502_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1501_, v___x_1498_, v_env_1478_, v_declName_1479_, v_asyncMode_1500_, v___x_1489_);
lean_dec(v_asyncMode_1500_);
if (lean_obj_tag(v___x_1502_) == 0)
{
if (v_includeBuiltin_1480_ == 0)
{
lean_dec(v_declName_1479_);
goto v___jp_1482_;
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1504_ = lean_st_ref_get(v___x_1503_);
v___x_1505_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1504_, v_declName_1479_);
lean_dec(v___x_1504_);
if (lean_obj_tag(v___x_1505_) == 1)
{
lean_object* v_val_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_declName_1479_);
v_val_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_val_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_val_1506_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1510_);
v___x_1512_ = v___x_1508_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec(v___x_1505_);
v___x_1516_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1517_ = lean_st_ref_get(v___x_1516_);
v___x_1518_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1517_, v_declName_1479_);
lean_dec(v_declName_1479_);
lean_dec(v___x_1517_);
if (lean_obj_tag(v___x_1518_) == 1)
{
lean_object* v_val_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1528_; 
v_val_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_val_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_val_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1523_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
}
else
{
lean_dec(v___x_1518_);
goto v___jp_1482_;
}
}
}
}
else
{
lean_object* v_val_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_declName_1479_);
v_val_1529_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1531_ = v___x_1502_;
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_val_1529_);
lean_dec(v___x_1502_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1533_, 0, v_val_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
return v___x_1536_;
}
}
}
}
else
{
lean_object* v_val_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v_declName_1479_);
lean_dec_ref(v_env_1478_);
v_val_1539_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1541_ = v___x_1497_;
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_val_1539_);
lean_dec(v___x_1497_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_val_1539_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1543_);
v___x_1545_ = v___x_1541_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
}
}
}
v___jp_1482_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_box(0);
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object* v_env_1549_, lean_object* v_declName_1550_, lean_object* v_includeBuiltin_1551_, lean_object* v_a_1552_){
_start:
{
uint8_t v_includeBuiltin_boxed_1553_; lean_object* v_res_1554_; 
v_includeBuiltin_boxed_1553_ = lean_unbox(v_includeBuiltin_1551_);
v_res_1554_ = l_Lean_findInternalDocString_x3f(v_env_1549_, v_declName_1550_, v_includeBuiltin_boxed_1553_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(lean_object* v_s_1555_, lean_object* v_replacement_1556_, lean_object* v_a_1557_, lean_object* v_b_1558_){
_start:
{
lean_object* v_it_1560_; lean_object* v_startPos_1561_; lean_object* v_endPos_1562_; lean_object* v_it_1571_; 
switch(lean_obj_tag(v_a_1557_))
{
case 0:
{
lean_object* v_pos_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1589_; 
v_pos_1577_ = lean_ctor_get(v_a_1557_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1579_ = v_a_1557_;
v_isShared_1580_ = v_isSharedCheck_1589_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_pos_1577_);
lean_dec(v_a_1557_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1589_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_startInclusive_1581_; lean_object* v_endExclusive_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v_startInclusive_1581_ = lean_ctor_get(v_s_1555_, 1);
v_endExclusive_1582_ = lean_ctor_get(v_s_1555_, 2);
v___x_1583_ = lean_nat_sub(v_endExclusive_1582_, v_startInclusive_1581_);
v___x_1584_ = lean_nat_dec_eq(v_pos_1577_, v___x_1583_);
lean_dec(v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1586_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 1);
v___x_1586_ = v___x_1579_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_pos_1577_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
v_it_1571_ = v___x_1586_;
goto v___jp_1570_;
}
}
else
{
lean_object* v___x_1588_; 
lean_del_object(v___x_1579_);
lean_dec(v_pos_1577_);
v___x_1588_ = lean_box(3);
v_it_1571_ = v___x_1588_;
goto v___jp_1570_;
}
}
}
case 1:
{
lean_object* v_pos_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1602_; 
v_pos_1590_ = lean_ctor_get(v_a_1557_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1592_ = v_a_1557_;
v_isShared_1593_ = v_isSharedCheck_1602_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_pos_1590_);
lean_dec(v_a_1557_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1602_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_str_1594_; lean_object* v_startInclusive_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v_str_1594_ = lean_ctor_get(v_s_1555_, 0);
v_startInclusive_1595_ = lean_ctor_get(v_s_1555_, 1);
v___x_1596_ = lean_nat_add(v_startInclusive_1595_, v_pos_1590_);
v___x_1597_ = lean_string_utf8_next_fast(v_str_1594_, v___x_1596_);
lean_dec(v___x_1596_);
v___x_1598_ = lean_nat_sub(v___x_1597_, v_startInclusive_1595_);
lean_inc(v___x_1598_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1598_);
v___x_1600_ = v___x_1592_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
v_it_1560_ = v___x_1600_;
v_startPos_1561_ = v_pos_1590_;
v_endPos_1562_ = v___x_1598_;
goto v___jp_1559_;
}
}
}
case 2:
{
lean_object* v_needle_1603_; lean_object* v_table_1604_; lean_object* v_stackPos_1605_; lean_object* v_needlePos_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1665_; 
v_needle_1603_ = lean_ctor_get(v_a_1557_, 0);
v_table_1604_ = lean_ctor_get(v_a_1557_, 1);
v_stackPos_1605_ = lean_ctor_get(v_a_1557_, 2);
v_needlePos_1606_ = lean_ctor_get(v_a_1557_, 3);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1608_ = v_a_1557_;
v_isShared_1609_ = v_isSharedCheck_1665_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_needlePos_1606_);
lean_inc(v_stackPos_1605_);
lean_inc(v_table_1604_);
lean_inc(v_needle_1603_);
lean_dec(v_a_1557_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1665_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v_str_1610_; lean_object* v_startInclusive_1611_; lean_object* v_endExclusive_1612_; lean_object* v_str_1613_; lean_object* v_startInclusive_1614_; lean_object* v_endExclusive_1615_; lean_object* v_basePos_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_str_1610_ = lean_ctor_get(v_needle_1603_, 0);
v_startInclusive_1611_ = lean_ctor_get(v_needle_1603_, 1);
v_endExclusive_1612_ = lean_ctor_get(v_needle_1603_, 2);
v_str_1613_ = lean_ctor_get(v_s_1555_, 0);
v_startInclusive_1614_ = lean_ctor_get(v_s_1555_, 1);
v_endExclusive_1615_ = lean_ctor_get(v_s_1555_, 2);
v_basePos_1616_ = lean_nat_sub(v_stackPos_1605_, v_needlePos_1606_);
v___x_1617_ = lean_nat_sub(v_endExclusive_1612_, v_startInclusive_1611_);
v___x_1618_ = lean_nat_add(v_basePos_1616_, v___x_1617_);
v___x_1619_ = lean_nat_sub(v_endExclusive_1615_, v_startInclusive_1614_);
v___x_1620_ = lean_nat_dec_le(v___x_1618_, v___x_1619_);
lean_dec(v___x_1618_);
if (v___x_1620_ == 0)
{
uint8_t v___x_1621_; 
lean_dec(v___x_1617_);
lean_del_object(v___x_1608_);
lean_dec(v_needlePos_1606_);
lean_dec(v_stackPos_1605_);
lean_dec_ref(v_table_1604_);
lean_dec_ref(v_needle_1603_);
v___x_1621_ = l_String_instDecidableLtRaw___aux__1(v_basePos_1616_, v___x_1619_);
if (v___x_1621_ == 0)
{
lean_dec(v___x_1619_);
lean_dec(v_basePos_1616_);
lean_dec_ref(v_s_1555_);
return v_b_1558_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = l_String_Slice_pos_x21(v_s_1555_, v_basePos_1616_);
lean_dec(v_basePos_1616_);
v___x_1623_ = lean_box(3);
v_it_1560_ = v___x_1623_;
v_startPos_1561_ = v___x_1622_;
v_endPos_1562_ = v___x_1619_;
goto v___jp_1559_;
}
}
else
{
lean_object* v___x_1624_; uint8_t v_stackByte_1625_; lean_object* v___x_1626_; uint8_t v_patByte_1627_; uint8_t v___x_1628_; 
lean_dec(v___x_1619_);
v___x_1624_ = lean_nat_add(v_startInclusive_1614_, v_stackPos_1605_);
v_stackByte_1625_ = lean_string_get_byte_fast(v_str_1613_, v___x_1624_);
v___x_1626_ = lean_nat_add(v_startInclusive_1611_, v_needlePos_1606_);
v_patByte_1627_ = lean_string_get_byte_fast(v_str_1610_, v___x_1626_);
v___x_1628_ = lean_uint8_dec_eq(v_stackByte_1625_, v_patByte_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
lean_dec(v___x_1617_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_nat_dec_eq(v_needlePos_1606_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_newNeedlePos_1633_; uint8_t v___x_1634_; 
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = lean_nat_sub(v_needlePos_1606_, v___x_1631_);
lean_dec(v_needlePos_1606_);
v_newNeedlePos_1633_ = lean_array_fget_borrowed(v_table_1604_, v___x_1632_);
lean_dec(v___x_1632_);
v___x_1634_ = lean_nat_dec_eq(v_newNeedlePos_1633_, v___x_1629_);
if (v___x_1634_ == 0)
{
lean_object* v_oldBasePos_1635_; lean_object* v___x_1636_; lean_object* v_newBasePos_1637_; lean_object* v___x_1639_; 
lean_inc(v_newNeedlePos_1633_);
v_oldBasePos_1635_ = l_String_Slice_pos_x21(v_s_1555_, v_basePos_1616_);
lean_dec(v_basePos_1616_);
v___x_1636_ = lean_nat_sub(v_stackPos_1605_, v_newNeedlePos_1633_);
v_newBasePos_1637_ = l_String_Slice_pos_x21(v_s_1555_, v___x_1636_);
lean_dec(v___x_1636_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v_newNeedlePos_1633_);
v___x_1639_ = v___x_1608_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_needle_1603_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_table_1604_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_stackPos_1605_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_newNeedlePos_1633_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
v_it_1560_ = v___x_1639_;
v_startPos_1561_ = v_oldBasePos_1635_;
v_endPos_1562_ = v_newBasePos_1637_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_basePos_1641_; lean_object* v_nextStackPos_1642_; lean_object* v___x_1644_; 
v_basePos_1641_ = l_String_Slice_pos_x21(v_s_1555_, v_basePos_1616_);
lean_dec(v_basePos_1616_);
v_nextStackPos_1642_ = l_String_Slice_posGE___redArg(v_s_1555_, v_stackPos_1605_);
lean_inc(v_nextStackPos_1642_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v___x_1629_);
lean_ctor_set(v___x_1608_, 2, v_nextStackPos_1642_);
v___x_1644_ = v___x_1608_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_needle_1603_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_table_1604_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_nextStackPos_1642_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v___x_1629_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
v_it_1560_ = v___x_1644_;
v_startPos_1561_ = v_basePos_1641_;
v_endPos_1562_ = v_nextStackPos_1642_;
goto v___jp_1559_;
}
}
}
else
{
lean_object* v_basePos_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v_nextStackPos_1649_; lean_object* v___x_1651_; 
lean_dec(v_basePos_1616_);
lean_dec(v_needlePos_1606_);
v_basePos_1646_ = l_String_Slice_pos_x21(v_s_1555_, v_stackPos_1605_);
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_add(v_stackPos_1605_, v___x_1647_);
lean_dec(v_stackPos_1605_);
v_nextStackPos_1649_ = l_String_Slice_posGE___redArg(v_s_1555_, v___x_1648_);
lean_inc(v_nextStackPos_1649_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v___x_1629_);
lean_ctor_set(v___x_1608_, 2, v_nextStackPos_1649_);
v___x_1651_ = v___x_1608_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_needle_1603_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_table_1604_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_nextStackPos_1649_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v___x_1629_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
v_it_1560_ = v___x_1651_;
v_startPos_1561_ = v_basePos_1646_;
v_endPos_1562_ = v_nextStackPos_1649_;
goto v___jp_1559_;
}
}
}
else
{
lean_object* v___x_1653_; lean_object* v_nextStackPos_1654_; lean_object* v_nextNeedlePos_1655_; uint8_t v___x_1656_; 
lean_dec(v_basePos_1616_);
v___x_1653_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1654_ = lean_nat_add(v_stackPos_1605_, v___x_1653_);
lean_dec(v_stackPos_1605_);
v_nextNeedlePos_1655_ = lean_nat_add(v_needlePos_1606_, v___x_1653_);
lean_dec(v_needlePos_1606_);
v___x_1656_ = lean_nat_dec_eq(v_nextNeedlePos_1655_, v___x_1617_);
lean_dec(v___x_1617_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1658_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v_nextNeedlePos_1655_);
lean_ctor_set(v___x_1608_, 2, v_nextStackPos_1654_);
v___x_1658_ = v___x_1608_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_needle_1603_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_table_1604_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_nextStackPos_1654_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_nextNeedlePos_1655_);
v___x_1658_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
v_a_1557_ = v___x_1658_;
goto _start;
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_dec(v_nextNeedlePos_1655_);
v___x_1661_ = lean_unsigned_to_nat(0u);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v___x_1661_);
lean_ctor_set(v___x_1608_, 2, v_nextStackPos_1654_);
v___x_1663_ = v___x_1608_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_needle_1603_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_table_1604_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_nextStackPos_1654_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
v_it_1571_ = v___x_1663_;
goto v___jp_1570_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1555_);
return v_b_1558_;
}
}
v___jp_1559_:
{
lean_object* v___x_1563_; lean_object* v_str_1564_; lean_object* v_startInclusive_1565_; lean_object* v_endExclusive_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_inc_ref(v_s_1555_);
v___x_1563_ = l_String_Slice_slice_x21(v_s_1555_, v_startPos_1561_, v_endPos_1562_);
lean_dec(v_endPos_1562_);
lean_dec(v_startPos_1561_);
v_str_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc_ref(v_str_1564_);
v_startInclusive_1565_ = lean_ctor_get(v___x_1563_, 1);
lean_inc(v_startInclusive_1565_);
v_endExclusive_1566_ = lean_ctor_get(v___x_1563_, 2);
lean_inc(v_endExclusive_1566_);
lean_dec_ref(v___x_1563_);
v___x_1567_ = lean_string_utf8_extract(v_str_1564_, v_startInclusive_1565_, v_endExclusive_1566_);
lean_dec(v_endExclusive_1566_);
lean_dec(v_startInclusive_1565_);
lean_dec_ref(v_str_1564_);
v___x_1568_ = lean_string_append(v_b_1558_, v___x_1567_);
lean_dec_ref(v___x_1567_);
v_a_1557_ = v_it_1560_;
v_b_1558_ = v___x_1568_;
goto _start;
}
v___jp_1570_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_string_utf8_byte_size(v_replacement_1556_);
v___x_1574_ = lean_string_utf8_extract(v_replacement_1556_, v___x_1572_, v___x_1573_);
v___x_1575_ = lean_string_append(v_b_1558_, v___x_1574_);
lean_dec_ref(v___x_1574_);
v_a_1557_ = v_it_1571_;
v_b_1558_ = v___x_1575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_s_1666_, lean_object* v_replacement_1667_, lean_object* v_a_1668_, lean_object* v_b_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1666_, v_replacement_1667_, v_a_1668_, v_b_1669_);
lean_dec_ref(v_replacement_1667_);
return v_res_1670_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1673_ = lean_string_utf8_byte_size(v___x_1672_);
return v___x_1673_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1676_ = lean_nat_dec_eq(v___x_1675_, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v___x_1678_);
lean_ctor_set(v___x_1680_, 2, v___x_1677_);
return v___x_1680_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1682_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1681_);
return v___x_1682_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4);
v___x_1685_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1686_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v___x_1684_);
lean_ctor_set(v___x_1686_, 2, v___x_1683_);
lean_ctor_set(v___x_1686_, 3, v___x_1683_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(lean_object* v_s_1689_, lean_object* v_replacement_1690_){
_start:
{
lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_1692_ = lean_uint8_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5);
v___x_1694_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1689_, v_replacement_1690_, v___x_1693_, v___x_1691_);
return v___x_1694_;
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__6));
v___x_1696_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1689_, v_replacement_1690_, v___x_1695_, v___x_1691_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_s_1697_, lean_object* v_replacement_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v_s_1697_, v_replacement_1698_);
lean_dec_ref(v_replacement_1698_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(lean_object* v_as_1707_, size_t v_sz_1708_, size_t v_i_1709_, lean_object* v_b_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_usize_dec_lt(v_i_1709_, v_sz_1708_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_b_1710_);
lean_ctor_set(v___x_1714_, 1, v___y_1712_);
return v___x_1714_;
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1716_; lean_object* v_snd_1717_; lean_object* v___x_1718_; size_t v___x_1719_; size_t v___x_1720_; 
v_a_1715_ = lean_array_uget_borrowed(v_as_1707_, v_i_1709_);
lean_inc(v_a_1715_);
v___x_1716_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_a_1715_, v___y_1711_, v___y_1712_);
v_snd_1717_ = lean_ctor_get(v___x_1716_, 1);
lean_inc(v_snd_1717_);
lean_dec_ref(v___x_1716_);
v___x_1718_ = lean_box(0);
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1709_, v___x_1719_);
v_i_1709_ = v___x_1720_;
v_b_1710_ = v___x_1718_;
v___y_1712_ = v_snd_1717_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__12));
v___x_1732_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_1733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
lean_ctor_set(v___x_1733_, 2, v___x_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(lean_object* v_x_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
switch(lean_obj_tag(v_x_1735_))
{
case 0:
{
lean_object* v_string_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_string_1738_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_string_1738_);
lean_dec_ref(v_x_1735_);
v___x_1739_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1738_);
lean_dec_ref(v_string_1738_);
v___x_1740_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1739_, v_a_1737_);
lean_dec_ref(v___x_1739_);
return v___x_1740_;
}
case 1:
{
lean_object* v_content_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1782_; 
v_content_1741_ = lean_ctor_get(v_x_1735_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_x_1735_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1743_ = v_x_1735_;
v_isShared_1744_ = v_isSharedCheck_1782_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_content_1741_);
lean_dec(v_x_1735_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1782_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set_tag(v___x_1743_, 9);
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_content_1741_);
v___x_1746_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; lean_object* v_snd_1748_; lean_object* v_fst_1749_; lean_object* v_fst_1750_; lean_object* v_snd_1751_; uint8_t v_inEmph_1753_; uint8_t v_inBold_1754_; uint8_t v_inLink_1755_; lean_object* v_linePrefix_1756_; lean_object* v___y_1757_; lean_object* v___x_1768_; uint8_t v_inEmph_1769_; 
v___x_1747_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1746_);
v_snd_1748_ = lean_ctor_get(v___x_1747_, 1);
lean_inc(v_snd_1748_);
v_fst_1749_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_fst_1749_);
lean_dec_ref(v___x_1747_);
v_fst_1750_ = lean_ctor_get(v_snd_1748_, 0);
lean_inc(v_fst_1750_);
v_snd_1751_ = lean_ctor_get(v_snd_1748_, 1);
lean_inc(v_snd_1751_);
lean_dec(v_snd_1748_);
v___x_1768_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1749_, v_a_1737_);
lean_dec(v_fst_1749_);
v_inEmph_1769_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1);
if (v_inEmph_1769_ == 0)
{
lean_object* v_snd_1770_; uint8_t v_inBold_1771_; uint8_t v_inLink_1772_; lean_object* v_linePrefix_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v_snd_1776_; 
v_snd_1770_ = lean_ctor_get(v___x_1768_, 1);
lean_inc(v_snd_1770_);
lean_dec_ref(v___x_1768_);
v_inBold_1771_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 1);
v_inLink_1772_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 2);
v_linePrefix_1773_ = lean_ctor_get(v_a_1736_, 0);
v___x_1774_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0));
v___x_1775_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1774_, v_snd_1770_);
v_snd_1776_ = lean_ctor_get(v___x_1775_, 1);
lean_inc(v_snd_1776_);
lean_dec_ref(v___x_1775_);
v_inEmph_1753_ = v_inEmph_1769_;
v_inBold_1754_ = v_inBold_1771_;
v_inLink_1755_ = v_inLink_1772_;
v_linePrefix_1756_ = v_linePrefix_1773_;
v___y_1757_ = v_snd_1776_;
goto v___jp_1752_;
}
else
{
lean_object* v_snd_1777_; uint8_t v_inBold_1778_; uint8_t v_inLink_1779_; lean_object* v_linePrefix_1780_; 
v_snd_1777_ = lean_ctor_get(v___x_1768_, 1);
lean_inc(v_snd_1777_);
lean_dec_ref(v___x_1768_);
v_inBold_1778_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 1);
v_inLink_1779_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 2);
v_linePrefix_1780_ = lean_ctor_get(v_a_1736_, 0);
v_inEmph_1753_ = v_inEmph_1769_;
v_inBold_1754_ = v_inBold_1778_;
v_inLink_1755_ = v_inLink_1779_;
v_linePrefix_1756_ = v_linePrefix_1780_;
v___y_1757_ = v_snd_1777_;
goto v___jp_1752_;
}
v___jp_1752_:
{
uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = 1;
lean_inc_ref(v_linePrefix_1756_);
v___x_1759_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1759_, 0, v_linePrefix_1756_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*1, v___x_1758_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*1 + 1, v_inBold_1754_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*1 + 2, v_inLink_1755_);
v___x_1760_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_fst_1750_, v___x_1759_, v___y_1757_);
lean_dec_ref(v___x_1759_);
if (v_inEmph_1753_ == 0)
{
lean_object* v_snd_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v_snd_1764_; lean_object* v___x_1765_; 
v_snd_1761_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_snd_1761_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0));
v___x_1763_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1762_, v_snd_1761_);
v_snd_1764_ = lean_ctor_get(v___x_1763_, 1);
lean_inc(v_snd_1764_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1751_, v_snd_1764_);
lean_dec(v_snd_1751_);
return v___x_1765_;
}
else
{
lean_object* v_snd_1766_; lean_object* v___x_1767_; 
v_snd_1766_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_snd_1766_);
lean_dec_ref(v___x_1760_);
v___x_1767_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1751_, v_snd_1766_);
lean_dec(v_snd_1751_);
return v___x_1767_;
}
}
}
}
}
case 2:
{
lean_object* v_content_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1821_; 
v_content_1783_ = lean_ctor_get(v_x_1735_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_x_1735_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1785_ = v_x_1735_;
v_isShared_1786_ = v_isSharedCheck_1821_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_content_1783_);
lean_dec(v_x_1735_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1821_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 9);
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_content_1783_);
v___x_1788_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; lean_object* v_snd_1790_; lean_object* v_fst_1791_; lean_object* v_fst_1792_; lean_object* v_snd_1793_; uint8_t v_inBold_1795_; uint8_t v_inLink_1796_; lean_object* v_linePrefix_1797_; lean_object* v___y_1798_; lean_object* v___x_1809_; uint8_t v_inBold_1810_; 
v___x_1789_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1788_);
v_snd_1790_ = lean_ctor_get(v___x_1789_, 1);
lean_inc(v_snd_1790_);
v_fst_1791_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_fst_1791_);
lean_dec_ref(v___x_1789_);
v_fst_1792_ = lean_ctor_get(v_snd_1790_, 0);
lean_inc(v_fst_1792_);
v_snd_1793_ = lean_ctor_get(v_snd_1790_, 1);
lean_inc(v_snd_1793_);
lean_dec(v_snd_1790_);
v___x_1809_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1791_, v_a_1737_);
lean_dec(v_fst_1791_);
v_inBold_1810_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 1);
if (v_inBold_1810_ == 0)
{
lean_object* v_snd_1811_; uint8_t v_inLink_1812_; lean_object* v_linePrefix_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v_snd_1816_; 
v_snd_1811_ = lean_ctor_get(v___x_1809_, 1);
lean_inc(v_snd_1811_);
lean_dec_ref(v___x_1809_);
v_inLink_1812_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 2);
v_linePrefix_1813_ = lean_ctor_get(v_a_1736_, 0);
v___x_1814_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1));
v___x_1815_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1814_, v_snd_1811_);
v_snd_1816_ = lean_ctor_get(v___x_1815_, 1);
lean_inc(v_snd_1816_);
lean_dec_ref(v___x_1815_);
v_inBold_1795_ = v_inBold_1810_;
v_inLink_1796_ = v_inLink_1812_;
v_linePrefix_1797_ = v_linePrefix_1813_;
v___y_1798_ = v_snd_1816_;
goto v___jp_1794_;
}
else
{
lean_object* v_snd_1817_; uint8_t v_inLink_1818_; lean_object* v_linePrefix_1819_; 
v_snd_1817_ = lean_ctor_get(v___x_1809_, 1);
lean_inc(v_snd_1817_);
lean_dec_ref(v___x_1809_);
v_inLink_1818_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 2);
v_linePrefix_1819_ = lean_ctor_get(v_a_1736_, 0);
v_inBold_1795_ = v_inBold_1810_;
v_inLink_1796_ = v_inLink_1818_;
v_linePrefix_1797_ = v_linePrefix_1819_;
v___y_1798_ = v_snd_1817_;
goto v___jp_1794_;
}
v___jp_1794_:
{
uint8_t v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = 1;
lean_inc_ref(v_linePrefix_1797_);
v___x_1800_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1800_, 0, v_linePrefix_1797_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*1, v___x_1799_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*1 + 1, v_inBold_1795_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*1 + 2, v_inLink_1796_);
v___x_1801_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_fst_1792_, v___x_1800_, v___y_1798_);
lean_dec_ref(v___x_1800_);
if (v_inBold_1795_ == 0)
{
lean_object* v_snd_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v_snd_1805_; lean_object* v___x_1806_; 
v_snd_1802_ = lean_ctor_get(v___x_1801_, 1);
lean_inc(v_snd_1802_);
lean_dec_ref(v___x_1801_);
v___x_1803_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1));
v___x_1804_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1803_, v_snd_1802_);
v_snd_1805_ = lean_ctor_get(v___x_1804_, 1);
lean_inc(v_snd_1805_);
lean_dec_ref(v___x_1804_);
v___x_1806_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1793_, v_snd_1805_);
lean_dec(v_snd_1793_);
return v___x_1806_;
}
else
{
lean_object* v_snd_1807_; lean_object* v___x_1808_; 
v_snd_1807_ = lean_ctor_get(v___x_1801_, 1);
lean_inc(v_snd_1807_);
lean_dec_ref(v___x_1801_);
v___x_1808_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1793_, v_snd_1807_);
lean_dec(v_snd_1793_);
return v___x_1808_;
}
}
}
}
}
case 3:
{
lean_object* v_string_1822_; lean_object* v___y_1824_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_fst_1829_; uint8_t v___x_1830_; 
v_string_1822_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_string_1822_);
lean_dec_ref(v_x_1735_);
v___x_1827_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__2));
v___x_1828_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v___x_1827_, v_a_1737_);
v_fst_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_fst_1829_);
v___x_1830_ = lean_unbox(v_fst_1829_);
lean_dec(v_fst_1829_);
if (v___x_1830_ == 0)
{
lean_object* v_snd_1831_; 
v_snd_1831_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_snd_1831_);
lean_dec_ref(v___x_1828_);
v___y_1824_ = v_snd_1831_;
goto v___jp_1823_;
}
else
{
lean_object* v_snd_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v_snd_1835_; 
v_snd_1832_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_snd_1832_);
lean_dec_ref(v___x_1828_);
v___x_1833_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__3));
v___x_1834_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1833_, v_snd_1832_);
v_snd_1835_ = lean_ctor_get(v___x_1834_, 1);
lean_inc(v_snd_1835_);
lean_dec_ref(v___x_1834_);
v___y_1824_ = v_snd_1835_;
goto v___jp_1823_;
}
v___jp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1822_);
v___x_1826_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1825_, v___y_1824_);
lean_dec_ref(v___x_1825_);
return v___x_1826_;
}
}
case 4:
{
uint8_t v_mode_1836_; 
v_mode_1836_ = lean_ctor_get_uint8(v_x_1735_, sizeof(void*)*1);
if (v_mode_1836_ == 0)
{
lean_object* v_string_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_string_1837_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_string_1837_);
lean_dec_ref(v_x_1735_);
v___x_1838_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__4));
v___x_1839_ = lean_string_append(v___x_1838_, v_string_1837_);
lean_dec_ref(v_string_1837_);
v___x_1840_ = lean_string_append(v___x_1839_, v___x_1838_);
v___x_1841_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1840_, v_a_1737_);
lean_dec_ref(v___x_1840_);
return v___x_1841_;
}
else
{
lean_object* v_string_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_string_1842_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_string_1842_);
lean_dec_ref(v_x_1735_);
v___x_1843_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__5));
v___x_1844_ = lean_string_append(v___x_1843_, v_string_1842_);
lean_dec_ref(v_string_1842_);
v___x_1845_ = lean_string_append(v___x_1844_, v___x_1843_);
v___x_1846_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1845_, v_a_1737_);
lean_dec_ref(v___x_1845_);
return v___x_1846_;
}
}
case 5:
{
lean_object* v_string_1847_; lean_object* v_linePrefix_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_string_1847_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_string_1847_);
lean_dec_ref(v_x_1735_);
v_linePrefix_1848_ = lean_ctor_get(v_a_1736_, 0);
v___x_1849_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1850_ = lean_string_append(v___x_1849_, v_linePrefix_1848_);
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_string_utf8_byte_size(v_string_1847_);
v___x_1853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1853_, 0, v_string_1847_);
lean_ctor_set(v___x_1853_, 1, v___x_1851_);
lean_ctor_set(v___x_1853_, 2, v___x_1852_);
v___x_1854_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v___x_1853_, v___x_1850_);
lean_dec_ref(v___x_1850_);
v___x_1855_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1854_, v_a_1737_);
lean_dec_ref(v___x_1854_);
return v___x_1855_;
}
case 6:
{
uint8_t v_inLink_1856_; 
v_inLink_1856_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 2);
if (v_inLink_1856_ == 0)
{
lean_object* v_content_1857_; lean_object* v_url_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_snd_1861_; lean_object* v___x_1862_; size_t v_sz_1863_; size_t v___x_1864_; lean_object* v___x_1865_; lean_object* v_snd_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v_snd_1869_; lean_object* v___x_1870_; lean_object* v_snd_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_content_1857_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_content_1857_);
v_url_1858_ = lean_ctor_get(v_x_1735_, 1);
lean_inc_ref(v_url_1858_);
lean_dec_ref(v_x_1735_);
v___x_1859_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__6));
v___x_1860_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1859_, v_a_1737_);
v_snd_1861_ = lean_ctor_get(v___x_1860_, 1);
lean_inc(v_snd_1861_);
lean_dec_ref(v___x_1860_);
v___x_1862_ = lean_box(0);
v_sz_1863_ = lean_array_size(v_content_1857_);
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1857_, v_sz_1863_, v___x_1864_, v___x_1862_, v_a_1736_, v_snd_1861_);
lean_dec_ref(v_content_1857_);
v_snd_1866_ = lean_ctor_get(v___x_1865_, 1);
lean_inc(v_snd_1866_);
lean_dec_ref(v___x_1865_);
v___x_1867_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7));
v___x_1868_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1867_, v_snd_1866_);
v_snd_1869_ = lean_ctor_get(v___x_1868_, 1);
lean_inc(v_snd_1869_);
lean_dec_ref(v___x_1868_);
v___x_1870_ = l_Lean_Doc_MarkdownM_push___redArg(v_url_1858_, v_snd_1869_);
lean_dec_ref(v_url_1858_);
v_snd_1871_ = lean_ctor_get(v___x_1870_, 1);
lean_inc(v_snd_1871_);
lean_dec_ref(v___x_1870_);
v___x_1872_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_1873_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1872_, v_snd_1871_);
return v___x_1873_;
}
else
{
lean_object* v_content_1874_; lean_object* v___x_1875_; size_t v_sz_1876_; size_t v___x_1877_; lean_object* v___x_1878_; lean_object* v_snd_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
v_content_1874_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_content_1874_);
lean_dec_ref(v_x_1735_);
v___x_1875_ = lean_box(0);
v_sz_1876_ = lean_array_size(v_content_1874_);
v___x_1877_ = ((size_t)0ULL);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1874_, v_sz_1876_, v___x_1877_, v___x_1875_, v_a_1736_, v_a_1737_);
lean_dec_ref(v_content_1874_);
v_snd_1879_ = lean_ctor_get(v___x_1878_, 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1886_ == 0)
{
lean_object* v_unused_1887_; 
v_unused_1887_ = lean_ctor_get(v___x_1878_, 0);
lean_dec(v_unused_1887_);
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_snd_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1875_);
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_snd_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
case 7:
{
lean_object* v_name_1888_; lean_object* v_content_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v_snd_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1934_; 
v_name_1888_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_name_1888_);
v_content_1889_ = lean_ctor_get(v_x_1735_, 1);
lean_inc_ref(v_content_1889_);
lean_dec_ref(v_x_1735_);
v___x_1890_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__9));
v___x_1891_ = lean_string_append(v___x_1890_, v_name_1888_);
v___x_1892_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10));
v___x_1893_ = lean_string_append(v___x_1891_, v___x_1892_);
v___x_1894_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1893_, v_a_1737_);
lean_dec_ref(v___x_1893_);
v_snd_1895_ = lean_ctor_get(v___x_1894_, 1);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v___x_1894_, 0);
lean_dec(v_unused_1935_);
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1934_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_snd_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1934_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_snd_1900_; lean_object* v___y_1919_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1921_ = lean_unsigned_to_nat(0u);
v___x_1922_ = lean_array_get_size(v_content_1889_);
v___x_1923_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11));
v___x_1924_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13);
v___x_1925_ = lean_nat_dec_lt(v___x_1921_, v___x_1922_);
if (v___x_1925_ == 0)
{
lean_dec_ref(v_content_1889_);
v_snd_1900_ = v___x_1924_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_nat_dec_le(v___x_1922_, v___x_1922_);
if (v___x_1927_ == 0)
{
if (v___x_1925_ == 0)
{
lean_dec_ref(v_content_1889_);
v_snd_1900_ = v___x_1924_;
goto v___jp_1899_;
}
else
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((size_t)0ULL);
v___x_1929_ = lean_usize_of_nat(v___x_1922_);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1889_, v___x_1928_, v___x_1929_, v___x_1926_, v___x_1923_, v___x_1924_);
lean_dec_ref(v_content_1889_);
v___y_1919_ = v___x_1930_;
goto v___jp_1918_;
}
}
else
{
size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = ((size_t)0ULL);
v___x_1932_ = lean_usize_of_nat(v___x_1922_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1889_, v___x_1931_, v___x_1932_, v___x_1926_, v___x_1923_, v___x_1924_);
lean_dec_ref(v_content_1889_);
v___y_1919_ = v___x_1933_;
goto v___jp_1918_;
}
}
v___jp_1899_:
{
lean_object* v_priorBlocks_1901_; lean_object* v_currentBlock_1902_; lean_object* v_footnotes_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1917_; 
v_priorBlocks_1901_ = lean_ctor_get(v_snd_1895_, 0);
v_currentBlock_1902_ = lean_ctor_get(v_snd_1895_, 1);
v_footnotes_1903_ = lean_ctor_get(v_snd_1895_, 2);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_snd_1895_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1905_ = v_snd_1895_;
v_isShared_1906_ = v_isSharedCheck_1917_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_footnotes_1903_);
lean_inc(v_currentBlock_1902_);
lean_inc(v_priorBlocks_1901_);
lean_dec(v_snd_1895_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1917_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1907_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_1900_);
v___x_1908_ = lean_box(0);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v___x_1907_);
lean_ctor_set(v___x_1897_, 0, v_name_1888_);
v___x_1910_ = v___x_1897_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_name_1888_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v___x_1907_);
v___x_1910_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1911_ = lean_array_push(v_footnotes_1903_, v___x_1910_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 2, v___x_1911_);
v___x_1913_ = v___x_1905_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_priorBlocks_1901_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_currentBlock_1902_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1908_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
return v___x_1914_;
}
}
}
}
v___jp_1918_:
{
lean_object* v_snd_1920_; 
v_snd_1920_ = lean_ctor_get(v___y_1919_, 1);
lean_inc(v_snd_1920_);
lean_dec_ref(v___y_1919_);
v_snd_1900_ = v_snd_1920_;
goto v___jp_1899_;
}
}
}
case 8:
{
lean_object* v_alt_1936_; lean_object* v_url_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_alt_1936_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_alt_1936_);
v_url_1937_ = lean_ctor_get(v_x_1735_, 1);
lean_inc_ref(v_url_1937_);
lean_dec_ref(v_x_1735_);
v___x_1938_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__14));
v___x_1939_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1936_);
lean_dec_ref(v_alt_1936_);
v___x_1940_ = lean_string_append(v___x_1938_, v___x_1939_);
lean_dec_ref(v___x_1939_);
v___x_1941_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7));
v___x_1942_ = lean_string_append(v___x_1940_, v___x_1941_);
v___x_1943_ = lean_string_append(v___x_1942_, v_url_1937_);
lean_dec_ref(v_url_1937_);
v___x_1944_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_1945_ = lean_string_append(v___x_1943_, v___x_1944_);
v___x_1946_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1945_, v_a_1737_);
lean_dec_ref(v___x_1945_);
return v___x_1946_;
}
case 9:
{
lean_object* v_content_1947_; lean_object* v___x_1948_; size_t v_sz_1949_; size_t v___x_1950_; lean_object* v___x_1951_; lean_object* v_snd_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_content_1947_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_content_1947_);
lean_dec_ref(v_x_1735_);
v___x_1948_ = lean_box(0);
v_sz_1949_ = lean_array_size(v_content_1947_);
v___x_1950_ = ((size_t)0ULL);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1947_, v_sz_1949_, v___x_1950_, v___x_1948_, v_a_1736_, v_a_1737_);
lean_dec_ref(v_content_1947_);
v_snd_1952_ = lean_ctor_get(v___x_1951_, 1);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v___x_1951_, 0);
lean_dec(v_unused_1960_);
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_snd_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1948_);
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_snd_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
default: 
{
lean_object* v_content_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_content_1961_ = lean_ctor_get(v_x_1735_, 1);
lean_inc_ref(v_content_1961_);
lean_dec_ref(v_x_1735_);
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = lean_array_get_size(v_content_1961_);
v___x_1964_ = lean_box(0);
v___x_1965_ = lean_nat_dec_lt(v___x_1962_, v___x_1963_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_dec_ref(v_content_1961_);
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v_a_1737_);
return v___x_1966_;
}
else
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_nat_dec_le(v___x_1963_, v___x_1963_);
if (v___x_1967_ == 0)
{
if (v___x_1965_ == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref(v_content_1961_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1964_);
lean_ctor_set(v___x_1968_, 1, v_a_1737_);
return v___x_1968_;
}
else
{
size_t v___x_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((size_t)0ULL);
v___x_1970_ = lean_usize_of_nat(v___x_1963_);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1961_, v___x_1969_, v___x_1970_, v___x_1964_, v_a_1736_, v_a_1737_);
lean_dec_ref(v_content_1961_);
return v___x_1971_;
}
}
else
{
size_t v___x_1972_; size_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = ((size_t)0ULL);
v___x_1973_ = lean_usize_of_nat(v___x_1963_);
v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1961_, v___x_1972_, v___x_1973_, v___x_1964_, v_a_1736_, v_a_1737_);
lean_dec_ref(v_content_1961_);
return v___x_1974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(lean_object* v_as_1975_, size_t v_i_1976_, size_t v_stop_1977_, lean_object* v_b_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
uint8_t v___x_1981_; 
v___x_1981_ = lean_usize_dec_eq(v_i_1976_, v_stop_1977_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_fst_1984_; lean_object* v_snd_1985_; size_t v___x_1986_; size_t v___x_1987_; 
v___x_1982_ = lean_array_uget_borrowed(v_as_1975_, v_i_1976_);
lean_inc(v___x_1982_);
v___x_1983_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_1982_, v___y_1979_, v___y_1980_);
v_fst_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_fst_1984_);
v_snd_1985_ = lean_ctor_get(v___x_1983_, 1);
lean_inc(v_snd_1985_);
lean_dec_ref(v___x_1983_);
v___x_1986_ = ((size_t)1ULL);
v___x_1987_ = lean_usize_add(v_i_1976_, v___x_1986_);
v_i_1976_ = v___x_1987_;
v_b_1978_ = v_fst_1984_;
v___y_1980_ = v_snd_1985_;
goto _start;
}
else
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_b_1978_);
lean_ctor_set(v___x_1989_, 1, v___y_1980_);
return v___x_1989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1990_, lean_object* v_i_1991_, lean_object* v_stop_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
size_t v_i_boxed_1996_; size_t v_stop_boxed_1997_; lean_object* v_res_1998_; 
v_i_boxed_1996_ = lean_unbox_usize(v_i_1991_);
lean_dec(v_i_1991_);
v_stop_boxed_1997_ = lean_unbox_usize(v_stop_1992_);
lean_dec(v_stop_1992_);
v_res_1998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_as_1990_, v_i_boxed_1996_, v_stop_boxed_1997_, v_b_1993_, v___y_1994_, v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec_ref(v_as_1990_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2___boxed(lean_object* v_as_1999_, lean_object* v_sz_2000_, lean_object* v_i_2001_, lean_object* v_b_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
size_t v_sz_boxed_2005_; size_t v_i_boxed_2006_; lean_object* v_res_2007_; 
v_sz_boxed_2005_ = lean_unbox_usize(v_sz_2000_);
lean_dec(v_sz_2000_);
v_i_boxed_2006_ = lean_unbox_usize(v_i_2001_);
lean_dec(v_i_2001_);
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_as_1999_, v_sz_boxed_2005_, v_i_boxed_2006_, v_b_2002_, v___y_2003_, v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec_ref(v_as_1999_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___boxed(lean_object* v_x_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_x_2008_, v_a_2009_, v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(lean_object* v_as_2014_, size_t v_sz_2015_, size_t v_i_2016_, lean_object* v_b_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v___x_2020_; 
v___x_2020_ = lean_usize_dec_lt(v_i_2016_, v_sz_2015_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v_b_2017_);
lean_ctor_set(v___x_2021_, 1, v___y_2019_);
return v___x_2021_;
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2023_; lean_object* v_snd_2024_; lean_object* v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; 
v_a_2022_ = lean_array_uget_borrowed(v_as_2014_, v_i_2016_);
lean_inc(v_a_2022_);
v___x_2023_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_a_2022_, v___y_2018_, v___y_2019_);
v_snd_2024_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_snd_2024_);
lean_dec_ref(v___x_2023_);
v___x_2025_ = lean_box(0);
v___x_2026_ = ((size_t)1ULL);
v___x_2027_ = lean_usize_add(v_i_2016_, v___x_2026_);
v_i_2016_ = v___x_2027_;
v_b_2017_ = v___x_2025_;
v___y_2019_ = v_snd_2024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(lean_object* v_as_2029_, size_t v_sz_2030_, size_t v_i_2031_, lean_object* v_b_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_usize_dec_lt(v_i_2031_, v_sz_2030_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2036_, 0, v_b_2032_);
lean_ctor_set(v___x_2036_, 1, v___y_2034_);
return v___x_2036_;
}
else
{
uint8_t v_inEmph_2037_; uint8_t v_inBold_2038_; uint8_t v_inLink_2039_; lean_object* v_linePrefix_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v_snd_2044_; lean_object* v___x_2045_; lean_object* v_a_2046_; size_t v_sz_2047_; size_t v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v_snd_2053_; size_t v___x_2054_; size_t v___x_2055_; 
v_inEmph_2037_ = lean_ctor_get_uint8(v___y_2033_, sizeof(void*)*1);
v_inBold_2038_ = lean_ctor_get_uint8(v___y_2033_, sizeof(void*)*1 + 1);
v_inLink_2039_ = lean_ctor_get_uint8(v___y_2033_, sizeof(void*)*1 + 2);
v_linePrefix_2040_ = lean_ctor_get(v___y_2033_, 0);
v___x_2041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0));
lean_inc_ref(v_linePrefix_2040_);
v___x_2042_ = lean_string_append(v_linePrefix_2040_, v___x_2041_);
v___x_2043_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2042_, v___y_2034_);
lean_dec_ref(v___x_2042_);
v_snd_2044_ = lean_ctor_get(v___x_2043_, 1);
lean_inc(v_snd_2044_);
lean_dec_ref(v___x_2043_);
v___x_2045_ = lean_box(0);
v_a_2046_ = lean_array_uget_borrowed(v_as_2029_, v_i_2031_);
v_sz_2047_ = lean_array_size(v_a_2046_);
v___x_2048_ = ((size_t)0ULL);
v___x_2049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
lean_inc_ref(v_linePrefix_2040_);
v___x_2050_ = lean_string_append(v_linePrefix_2040_, v___x_2049_);
v___x_2051_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*1, v_inEmph_2037_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*1 + 1, v_inBold_2038_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*1 + 2, v_inLink_2039_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2046_, v_sz_2047_, v___x_2048_, v___x_2045_, v___x_2051_, v_snd_2044_);
lean_dec_ref(v___x_2051_);
v_snd_2053_ = lean_ctor_get(v___x_2052_, 1);
lean_inc(v_snd_2053_);
lean_dec_ref(v___x_2052_);
v___x_2054_ = ((size_t)1ULL);
v___x_2055_ = lean_usize_add(v_i_2031_, v___x_2054_);
v_i_2031_ = v___x_2055_;
v_b_2032_ = v___x_2045_;
v___y_2034_ = v_snd_2053_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(lean_object* v_as_2058_, size_t v_sz_2059_, size_t v_i_2060_, lean_object* v_b_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
uint8_t v___x_2064_; 
v___x_2064_ = lean_usize_dec_lt(v_i_2060_, v_sz_2059_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v_b_2061_);
lean_ctor_set(v___x_2065_, 1, v___y_2063_);
return v___x_2065_;
}
else
{
uint8_t v_inEmph_2066_; uint8_t v_inBold_2067_; uint8_t v_inLink_2068_; lean_object* v_linePrefix_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v_snd_2075_; lean_object* v_a_2076_; lean_object* v___x_2077_; size_t v_sz_2078_; size_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v_snd_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; size_t v___x_2087_; size_t v___x_2088_; 
v_inEmph_2066_ = lean_ctor_get_uint8(v___y_2062_, sizeof(void*)*1);
v_inBold_2067_ = lean_ctor_get_uint8(v___y_2062_, sizeof(void*)*1 + 1);
v_inLink_2068_ = lean_ctor_get_uint8(v___y_2062_, sizeof(void*)*1 + 2);
v_linePrefix_2069_ = lean_ctor_get(v___y_2062_, 0);
lean_inc(v_b_2061_);
v___x_2070_ = l_Nat_reprFast(v_b_2061_);
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0));
v___x_2072_ = lean_string_append(v___x_2070_, v___x_2071_);
lean_inc_ref(v_linePrefix_2069_);
v___x_2073_ = lean_string_append(v_linePrefix_2069_, v___x_2072_);
lean_dec_ref(v___x_2072_);
v___x_2074_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2073_, v___y_2063_);
lean_dec_ref(v___x_2073_);
v_snd_2075_ = lean_ctor_get(v___x_2074_, 1);
lean_inc(v_snd_2075_);
lean_dec_ref(v___x_2074_);
v_a_2076_ = lean_array_uget_borrowed(v_as_2058_, v_i_2060_);
v___x_2077_ = lean_box(0);
v_sz_2078_ = lean_array_size(v_a_2076_);
v___x_2079_ = ((size_t)0ULL);
v___x_2080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
lean_inc_ref(v_linePrefix_2069_);
v___x_2081_ = lean_string_append(v_linePrefix_2069_, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*1, v_inEmph_2066_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*1 + 1, v_inBold_2067_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*1 + 2, v_inLink_2068_);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2076_, v_sz_2078_, v___x_2079_, v___x_2077_, v___x_2082_, v_snd_2075_);
lean_dec_ref(v___x_2082_);
v_snd_2084_ = lean_ctor_get(v___x_2083_, 1);
lean_inc(v_snd_2084_);
lean_dec_ref(v___x_2083_);
v___x_2085_ = lean_unsigned_to_nat(1u);
v___x_2086_ = lean_nat_add(v_b_2061_, v___x_2085_);
lean_dec(v_b_2061_);
v___x_2087_ = ((size_t)1ULL);
v___x_2088_ = lean_usize_add(v_i_2060_, v___x_2087_);
v_i_2060_ = v___x_2088_;
v_b_2061_ = v___x_2086_;
v___y_2063_ = v_snd_2084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(lean_object* v_as_2093_, size_t v_sz_2094_, size_t v_i_2095_, lean_object* v_b_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_usize_dec_lt(v_i_2095_, v_sz_2094_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v_b_2096_);
lean_ctor_set(v___x_2100_, 1, v___y_2098_);
return v___x_2100_;
}
else
{
uint8_t v_inEmph_2101_; uint8_t v_inBold_2102_; uint8_t v_inLink_2103_; lean_object* v_linePrefix_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v_snd_2108_; lean_object* v_a_2109_; lean_object* v_term_2110_; lean_object* v_desc_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v_snd_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_snd_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v_snd_2123_; lean_object* v___x_2124_; lean_object* v_snd_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v_snd_2128_; lean_object* v___x_2129_; size_t v___x_2130_; size_t v___x_2131_; 
v_inEmph_2101_ = lean_ctor_get_uint8(v___y_2097_, sizeof(void*)*1);
v_inBold_2102_ = lean_ctor_get_uint8(v___y_2097_, sizeof(void*)*1 + 1);
v_inLink_2103_ = lean_ctor_get_uint8(v___y_2097_, sizeof(void*)*1 + 2);
v_linePrefix_2104_ = lean_ctor_get(v___y_2097_, 0);
v___x_2105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0));
lean_inc_ref(v_linePrefix_2104_);
v___x_2106_ = lean_string_append(v_linePrefix_2104_, v___x_2105_);
v___x_2107_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2106_, v___y_2098_);
lean_dec_ref(v___x_2106_);
v_snd_2108_ = lean_ctor_get(v___x_2107_, 1);
lean_inc(v_snd_2108_);
lean_dec_ref(v___x_2107_);
v_a_2109_ = lean_array_uget_borrowed(v_as_2093_, v_i_2095_);
v_term_2110_ = lean_ctor_get(v_a_2109_, 0);
v_desc_2111_ = lean_ctor_get(v_a_2109_, 1);
lean_inc_ref(v_term_2110_);
v___x_2112_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_term_2110_);
v___x_2113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
lean_inc_ref(v_linePrefix_2104_);
v___x_2114_ = lean_string_append(v_linePrefix_2104_, v___x_2113_);
lean_inc_ref(v___x_2114_);
v___x_2115_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1, v_inEmph_2101_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1 + 1, v_inBold_2102_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1 + 2, v_inLink_2103_);
v___x_2116_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_2112_, v___x_2115_, v_snd_2108_);
v_snd_2117_ = lean_ctor_get(v___x_2116_, 1);
lean_inc(v_snd_2117_);
lean_dec_ref(v___x_2116_);
v___x_2118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__1));
v___x_2119_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_2118_, v___x_2115_, v_snd_2117_);
v_snd_2120_ = lean_ctor_get(v___x_2119_, 1);
lean_inc(v_snd_2120_);
lean_dec_ref(v___x_2119_);
v___x_2121_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2122_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2121_, v_snd_2120_);
v_snd_2123_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_snd_2123_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2114_, v_snd_2123_);
lean_dec_ref(v___x_2114_);
v_snd_2125_ = lean_ctor_get(v___x_2124_, 1);
lean_inc(v_snd_2125_);
lean_dec_ref(v___x_2124_);
lean_inc_ref(v_desc_2111_);
v___x_2126_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_desc_2111_);
v___x_2127_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2126_, v___x_2115_, v_snd_2125_);
lean_dec_ref(v___x_2115_);
v_snd_2128_ = lean_ctor_get(v___x_2127_, 1);
lean_inc(v_snd_2128_);
lean_dec_ref(v___x_2127_);
v___x_2129_ = lean_box(0);
v___x_2130_ = ((size_t)1ULL);
v___x_2131_ = lean_usize_add(v_i_2095_, v___x_2130_);
v_i_2095_ = v___x_2131_;
v_b_2096_ = v___x_2129_;
v___y_2098_ = v_snd_2128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(lean_object* v_x_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
switch(lean_obj_tag(v_x_2134_))
{
case 0:
{
lean_object* v_contents_2137_; lean_object* v___x_2138_; size_t v_sz_2139_; size_t v___x_2140_; lean_object* v___x_2141_; lean_object* v_snd_2142_; lean_object* v___x_2143_; 
v_contents_2137_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_contents_2137_);
lean_dec_ref(v_x_2134_);
v___x_2138_ = lean_box(0);
v_sz_2139_ = lean_array_size(v_contents_2137_);
v___x_2140_ = ((size_t)0ULL);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_contents_2137_, v_sz_2139_, v___x_2140_, v___x_2138_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_contents_2137_);
v_snd_2142_ = lean_ctor_get(v___x_2141_, 1);
lean_inc(v_snd_2142_);
lean_dec_ref(v___x_2141_);
v___x_2143_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2142_);
return v___x_2143_;
}
case 1:
{
lean_object* v_content_2144_; lean_object* v___y_2146_; lean_object* v___y_2147_; uint8_t v___y_2155_; lean_object* v_currentBlock_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v_content_2144_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_content_2144_);
lean_dec_ref(v_x_2134_);
v_currentBlock_2159_ = lean_ctor_get(v_a_2136_, 1);
v___x_2160_ = lean_string_utf8_byte_size(v_currentBlock_2159_);
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = lean_nat_dec_eq(v___x_2160_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2163_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2164_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2165_ = lean_nat_dec_le(v___x_2164_, v___x_2160_);
if (v___x_2165_ == 0)
{
v___y_2155_ = v___x_2162_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_nat_sub(v___x_2160_, v___x_2164_);
v___x_2167_ = lean_string_memcmp(v_currentBlock_2159_, v___x_2163_, v___x_2166_, v___x_2161_, v___x_2164_);
lean_dec(v___x_2166_);
v___y_2155_ = v___x_2167_;
goto v___jp_2154_;
}
}
else
{
v___y_2155_ = v___x_2162_;
goto v___jp_2154_;
}
v___jp_2145_:
{
lean_object* v_linePrefix_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_snd_2152_; lean_object* v___x_2153_; 
v_linePrefix_2148_ = lean_ctor_get(v___y_2146_, 0);
v___x_2149_ = lean_string_length(v_linePrefix_2148_);
v___x_2150_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v___x_2149_, v_content_2144_);
lean_dec_ref(v_content_2144_);
v___x_2151_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2150_, v___y_2147_);
lean_dec_ref(v___x_2150_);
v_snd_2152_ = lean_ctor_get(v___x_2151_, 1);
lean_inc(v_snd_2152_);
lean_dec_ref(v___x_2151_);
v___x_2153_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2152_);
return v___x_2153_;
}
v___jp_2154_:
{
if (v___y_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v_snd_2158_; 
v___x_2156_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2157_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2156_, v_a_2136_);
v_snd_2158_ = lean_ctor_get(v___x_2157_, 1);
lean_inc(v_snd_2158_);
lean_dec_ref(v___x_2157_);
v___y_2146_ = v_a_2135_;
v___y_2147_ = v_snd_2158_;
goto v___jp_2145_;
}
else
{
v___y_2146_ = v_a_2135_;
v___y_2147_ = v_a_2136_;
goto v___jp_2145_;
}
}
}
case 2:
{
lean_object* v_items_2168_; lean_object* v___x_2169_; size_t v_sz_2170_; size_t v___x_2171_; lean_object* v___x_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; 
v_items_2168_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_items_2168_);
lean_dec_ref(v_x_2134_);
v___x_2169_ = lean_box(0);
v_sz_2170_ = lean_array_size(v_items_2168_);
v___x_2171_ = ((size_t)0ULL);
v___x_2172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_items_2168_, v_sz_2170_, v___x_2171_, v___x_2169_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_items_2168_);
v_snd_2173_ = lean_ctor_get(v___x_2172_, 1);
lean_inc(v_snd_2173_);
lean_dec_ref(v___x_2172_);
v___x_2174_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2173_);
return v___x_2174_;
}
case 3:
{
lean_object* v_start_2175_; lean_object* v_items_2176_; lean_object* v___y_2178_; lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v_start_2175_ = lean_ctor_get(v_x_2134_, 0);
lean_inc(v_start_2175_);
v_items_2176_ = lean_ctor_get(v_x_2134_, 1);
lean_inc_ref(v_items_2176_);
lean_dec_ref(v_x_2134_);
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = l_Int_toNat(v_start_2175_);
lean_dec(v_start_2175_);
v___x_2186_ = lean_nat_dec_le(v___x_2184_, v___x_2185_);
if (v___x_2186_ == 0)
{
lean_dec(v___x_2185_);
v___y_2178_ = v___x_2184_;
goto v___jp_2177_;
}
else
{
v___y_2178_ = v___x_2185_;
goto v___jp_2177_;
}
v___jp_2177_:
{
size_t v_sz_2179_; size_t v___x_2180_; lean_object* v___x_2181_; lean_object* v_snd_2182_; lean_object* v___x_2183_; 
v_sz_2179_ = lean_array_size(v_items_2176_);
v___x_2180_ = ((size_t)0ULL);
v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_items_2176_, v_sz_2179_, v___x_2180_, v___y_2178_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_items_2176_);
v_snd_2182_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_snd_2182_);
lean_dec_ref(v___x_2181_);
v___x_2183_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2182_);
return v___x_2183_;
}
}
case 4:
{
lean_object* v_items_2187_; lean_object* v___x_2188_; size_t v_sz_2189_; size_t v___x_2190_; lean_object* v___x_2191_; lean_object* v_snd_2192_; lean_object* v___x_2193_; 
v_items_2187_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_items_2187_);
lean_dec_ref(v_x_2134_);
v___x_2188_ = lean_box(0);
v_sz_2189_ = lean_array_size(v_items_2187_);
v___x_2190_ = ((size_t)0ULL);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_items_2187_, v_sz_2189_, v___x_2190_, v___x_2188_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_items_2187_);
v_snd_2192_ = lean_ctor_get(v___x_2191_, 1);
lean_inc(v_snd_2192_);
lean_dec_ref(v___x_2191_);
v___x_2193_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2192_);
return v___x_2193_;
}
case 5:
{
lean_object* v_items_2194_; uint8_t v_inEmph_2195_; uint8_t v_inBold_2196_; uint8_t v_inLink_2197_; lean_object* v_linePrefix_2198_; lean_object* v___x_2199_; size_t v_sz_2200_; size_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_snd_2206_; lean_object* v___x_2207_; 
v_items_2194_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_items_2194_);
lean_dec_ref(v_x_2134_);
v_inEmph_2195_ = lean_ctor_get_uint8(v_a_2135_, sizeof(void*)*1);
v_inBold_2196_ = lean_ctor_get_uint8(v_a_2135_, sizeof(void*)*1 + 1);
v_inLink_2197_ = lean_ctor_get_uint8(v_a_2135_, sizeof(void*)*1 + 2);
v_linePrefix_2198_ = lean_ctor_get(v_a_2135_, 0);
v___x_2199_ = lean_box(0);
v_sz_2200_ = lean_array_size(v_items_2194_);
v___x_2201_ = ((size_t)0ULL);
v___x_2202_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0));
lean_inc_ref(v_linePrefix_2198_);
v___x_2203_ = lean_string_append(v_linePrefix_2198_, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1, v_inEmph_2195_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1 + 1, v_inBold_2196_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1 + 2, v_inLink_2197_);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_items_2194_, v_sz_2200_, v___x_2201_, v___x_2199_, v___x_2204_, v_a_2136_);
lean_dec_ref(v___x_2204_);
lean_dec_ref(v_items_2194_);
v_snd_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_snd_2206_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2206_);
return v___x_2207_;
}
case 6:
{
lean_object* v_content_2208_; lean_object* v___x_2209_; size_t v_sz_2210_; size_t v___x_2211_; lean_object* v___x_2212_; lean_object* v_snd_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_content_2208_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_content_2208_);
lean_dec_ref(v_x_2134_);
v___x_2209_ = lean_box(0);
v_sz_2210_ = lean_array_size(v_content_2208_);
v___x_2211_ = ((size_t)0ULL);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2208_, v_sz_2210_, v___x_2211_, v___x_2209_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_content_2208_);
v_snd_2213_ = lean_ctor_get(v___x_2212_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v___x_2212_, 0);
lean_dec(v_unused_2221_);
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_snd_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2209_);
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_snd_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
default: 
{
lean_object* v_content_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2243_; 
v_content_2222_ = lean_ctor_get(v_x_2134_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_x_2134_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v_x_2134_, 0);
lean_dec(v_unused_2244_);
v___x_2224_ = v_x_2134_;
v_isShared_2225_ = v_isSharedCheck_2243_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_content_2222_);
lean_dec(v_x_2134_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2243_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = lean_array_get_size(v_content_2222_);
v___x_2228_ = lean_box(0);
v___x_2229_ = lean_nat_dec_lt(v___x_2226_, v___x_2227_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2231_; 
lean_dec_ref(v_content_2222_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 0);
lean_ctor_set(v___x_2224_, 1, v_a_2136_);
lean_ctor_set(v___x_2224_, 0, v___x_2228_);
v___x_2231_ = v___x_2224_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_a_2136_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
else
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_nat_dec_le(v___x_2227_, v___x_2227_);
if (v___x_2233_ == 0)
{
if (v___x_2229_ == 0)
{
lean_object* v___x_2235_; 
lean_dec_ref(v_content_2222_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 0);
lean_ctor_set(v___x_2224_, 1, v_a_2136_);
lean_ctor_set(v___x_2224_, 0, v___x_2228_);
v___x_2235_ = v___x_2224_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_a_2136_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
else
{
size_t v___x_2237_; size_t v___x_2238_; lean_object* v___x_2239_; 
lean_del_object(v___x_2224_);
v___x_2237_ = ((size_t)0ULL);
v___x_2238_ = lean_usize_of_nat(v___x_2227_);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_content_2222_, v___x_2237_, v___x_2238_, v___x_2228_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_content_2222_);
return v___x_2239_;
}
}
else
{
size_t v___x_2240_; size_t v___x_2241_; lean_object* v___x_2242_; 
lean_del_object(v___x_2224_);
v___x_2240_ = ((size_t)0ULL);
v___x_2241_ = lean_usize_of_nat(v___x_2227_);
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_content_2222_, v___x_2240_, v___x_2241_, v___x_2228_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_content_2222_);
return v___x_2242_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(lean_object* v_as_2245_, size_t v_i_2246_, size_t v_stop_2247_, lean_object* v_b_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_usize_dec_eq(v_i_2246_, v_stop_2247_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v_fst_2254_; lean_object* v_snd_2255_; size_t v___x_2256_; size_t v___x_2257_; 
v___x_2252_ = lean_array_uget_borrowed(v_as_2245_, v_i_2246_);
lean_inc(v___x_2252_);
v___x_2253_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2252_, v___y_2249_, v___y_2250_);
v_fst_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_fst_2254_);
v_snd_2255_ = lean_ctor_get(v___x_2253_, 1);
lean_inc(v_snd_2255_);
lean_dec_ref(v___x_2253_);
v___x_2256_ = ((size_t)1ULL);
v___x_2257_ = lean_usize_add(v_i_2246_, v___x_2256_);
v_i_2246_ = v___x_2257_;
v_b_2248_ = v_fst_2254_;
v___y_2250_ = v_snd_2255_;
goto _start;
}
else
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2259_, 0, v_b_2248_);
lean_ctor_set(v___x_2259_, 1, v___y_2250_);
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___boxed(lean_object* v_as_2260_, lean_object* v_i_2261_, lean_object* v_stop_2262_, lean_object* v_b_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
size_t v_i_boxed_2266_; size_t v_stop_boxed_2267_; lean_object* v_res_2268_; 
v_i_boxed_2266_ = lean_unbox_usize(v_i_2261_);
lean_dec(v_i_2261_);
v_stop_boxed_2267_ = lean_unbox_usize(v_stop_2262_);
lean_dec(v_stop_2262_);
v_res_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_as_2260_, v_i_boxed_2266_, v_stop_boxed_2267_, v_b_2263_, v___y_2264_, v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_as_2260_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2___boxed(lean_object* v_as_2269_, lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_b_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
size_t v_sz_boxed_2275_; size_t v_i_boxed_2276_; lean_object* v_res_2277_; 
v_sz_boxed_2275_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2276_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_as_2269_, v_sz_boxed_2275_, v_i_boxed_2276_, v_b_2272_, v___y_2273_, v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_as_2269_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___boxed(lean_object* v_as_2278_, lean_object* v_sz_2279_, lean_object* v_i_2280_, lean_object* v_b_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
size_t v_sz_boxed_2284_; size_t v_i_boxed_2285_; lean_object* v_res_2286_; 
v_sz_boxed_2284_ = lean_unbox_usize(v_sz_2279_);
lean_dec(v_sz_2279_);
v_i_boxed_2285_ = lean_unbox_usize(v_i_2280_);
lean_dec(v_i_2280_);
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_as_2278_, v_sz_boxed_2284_, v_i_boxed_2285_, v_b_2281_, v___y_2282_, v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec_ref(v_as_2278_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___boxed(lean_object* v_as_2287_, lean_object* v_sz_2288_, lean_object* v_i_2289_, lean_object* v_b_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
size_t v_sz_boxed_2293_; size_t v_i_boxed_2294_; lean_object* v_res_2295_; 
v_sz_boxed_2293_ = lean_unbox_usize(v_sz_2288_);
lean_dec(v_sz_2288_);
v_i_boxed_2294_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_as_2287_, v_sz_boxed_2293_, v_i_boxed_2294_, v_b_2290_, v___y_2291_, v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec_ref(v_as_2287_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___boxed(lean_object* v_as_2296_, lean_object* v_sz_2297_, lean_object* v_i_2298_, lean_object* v_b_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
size_t v_sz_boxed_2302_; size_t v_i_boxed_2303_; lean_object* v_res_2304_; 
v_sz_boxed_2302_ = lean_unbox_usize(v_sz_2297_);
lean_dec(v_sz_2297_);
v_i_boxed_2303_ = lean_unbox_usize(v_i_2298_);
lean_dec(v_i_2298_);
v_res_2304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_as_2296_, v_sz_boxed_2302_, v_i_boxed_2303_, v_b_2299_, v___y_2300_, v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec_ref(v_as_2296_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___boxed(lean_object* v_x_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_x_2305_, v_a_2306_, v_a_2307_);
lean_dec_ref(v_a_2306_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(lean_object* v_x_2309_, lean_object* v_x_2310_){
_start:
{
lean_object* v_zero_2311_; uint8_t v_isZero_2312_; 
v_zero_2311_ = lean_unsigned_to_nat(0u);
v_isZero_2312_ = lean_nat_dec_eq(v_x_2309_, v_zero_2311_);
if (v_isZero_2312_ == 1)
{
lean_dec(v_x_2309_);
return v_x_2310_;
}
else
{
uint32_t v___x_2313_; lean_object* v_one_2314_; lean_object* v_n_2315_; lean_object* v___x_2316_; 
v___x_2313_ = 35;
v_one_2314_ = lean_unsigned_to_nat(1u);
v_n_2315_ = lean_nat_sub(v_x_2309_, v_one_2314_);
lean_dec(v_x_2309_);
v___x_2316_ = lean_string_push(v_x_2310_, v___x_2313_);
v_x_2309_ = v_n_2315_;
v_x_2310_ = v___x_2316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(lean_object* v_level_2319_, lean_object* v_part_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v_snd_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v_snd_2331_; lean_object* v_title_2332_; lean_object* v_content_2333_; lean_object* v_subParts_2334_; lean_object* v___x_2335_; size_t v_sz_2336_; size_t v___x_2337_; lean_object* v___x_2338_; lean_object* v_snd_2339_; lean_object* v___x_2340_; lean_object* v_snd_2341_; size_t v_sz_2342_; lean_object* v___x_2343_; lean_object* v_snd_2344_; lean_object* v___x_2345_; lean_object* v_snd_2346_; size_t v_sz_2347_; lean_object* v___x_2348_; lean_object* v_snd_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
v___x_2323_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_2324_ = lean_unsigned_to_nat(1u);
v___x_2325_ = lean_nat_add(v_level_2319_, v___x_2324_);
lean_inc(v___x_2325_);
v___x_2326_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v___x_2325_, v___x_2323_);
v___x_2327_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2326_, v_a_2322_);
lean_dec_ref(v___x_2326_);
v_snd_2328_ = lean_ctor_get(v___x_2327_, 1);
lean_inc(v_snd_2328_);
lean_dec_ref(v___x_2327_);
v___x_2329_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0));
v___x_2330_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2329_, v_snd_2328_);
v_snd_2331_ = lean_ctor_get(v___x_2330_, 1);
lean_inc(v_snd_2331_);
lean_dec_ref(v___x_2330_);
v_title_2332_ = lean_ctor_get(v_part_2320_, 0);
v_content_2333_ = lean_ctor_get(v_part_2320_, 3);
v_subParts_2334_ = lean_ctor_get(v_part_2320_, 4);
v___x_2335_ = lean_box(0);
v_sz_2336_ = lean_array_size(v_title_2332_);
v___x_2337_ = ((size_t)0ULL);
v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_title_2332_, v_sz_2336_, v___x_2337_, v___x_2335_, v_a_2321_, v_snd_2331_);
v_snd_2339_ = lean_ctor_get(v___x_2338_, 1);
lean_inc(v_snd_2339_);
lean_dec_ref(v___x_2338_);
v___x_2340_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2339_);
v_snd_2341_ = lean_ctor_get(v___x_2340_, 1);
lean_inc(v_snd_2341_);
lean_dec_ref(v___x_2340_);
v_sz_2342_ = lean_array_size(v_content_2333_);
v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2333_, v_sz_2342_, v___x_2337_, v___x_2335_, v_a_2321_, v_snd_2341_);
v_snd_2344_ = lean_ctor_get(v___x_2343_, 1);
lean_inc(v_snd_2344_);
lean_dec_ref(v___x_2343_);
v___x_2345_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2344_);
v_snd_2346_ = lean_ctor_get(v___x_2345_, 1);
lean_inc(v_snd_2346_);
lean_dec_ref(v___x_2345_);
v_sz_2347_ = lean_array_size(v_subParts_2334_);
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2325_, v_subParts_2334_, v_sz_2347_, v___x_2337_, v___x_2335_, v_a_2321_, v_snd_2346_);
lean_dec(v___x_2325_);
v_snd_2349_ = lean_ctor_get(v___x_2348_, 1);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; 
v_unused_2357_ = lean_ctor_get(v___x_2348_, 0);
lean_dec(v_unused_2357_);
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_snd_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2335_);
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_snd_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(lean_object* v___x_2358_, lean_object* v_as_2359_, size_t v_sz_2360_, size_t v_i_2361_, lean_object* v_b_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v___x_2365_; 
v___x_2365_ = lean_usize_dec_lt(v_i_2361_, v_sz_2360_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_b_2362_);
lean_ctor_set(v___x_2366_, 1, v___y_2364_);
return v___x_2366_;
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2368_; lean_object* v_snd_2369_; lean_object* v___x_2370_; size_t v___x_2371_; size_t v___x_2372_; 
v_a_2367_ = lean_array_uget_borrowed(v_as_2359_, v_i_2361_);
v___x_2368_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2358_, v_a_2367_, v___y_2363_, v___y_2364_);
v_snd_2369_ = lean_ctor_get(v___x_2368_, 1);
lean_inc(v_snd_2369_);
lean_dec_ref(v___x_2368_);
v___x_2370_ = lean_box(0);
v___x_2371_ = ((size_t)1ULL);
v___x_2372_ = lean_usize_add(v_i_2361_, v___x_2371_);
v_i_2361_ = v___x_2372_;
v_b_2362_ = v___x_2370_;
v___y_2364_ = v_snd_2369_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg___boxed(lean_object* v___x_2374_, lean_object* v_as_2375_, lean_object* v_sz_2376_, lean_object* v_i_2377_, lean_object* v_b_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
size_t v_sz_boxed_2381_; size_t v_i_boxed_2382_; lean_object* v_res_2383_; 
v_sz_boxed_2381_ = lean_unbox_usize(v_sz_2376_);
lean_dec(v_sz_2376_);
v_i_boxed_2382_ = lean_unbox_usize(v_i_2377_);
lean_dec(v_i_2377_);
v_res_2383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2374_, v_as_2375_, v_sz_boxed_2381_, v_i_boxed_2382_, v_b_2378_, v___y_2379_, v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec_ref(v_as_2375_);
lean_dec(v___x_2374_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___boxed(lean_object* v_level_2384_, lean_object* v_part_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2384_, v_part_2385_, v_a_2386_, v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec_ref(v_part_2385_);
lean_dec(v_level_2384_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(lean_object* v_as_2389_, size_t v_sz_2390_, size_t v_i_2391_, lean_object* v_b_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
uint8_t v___x_2395_; 
v___x_2395_ = lean_usize_dec_lt(v_i_2391_, v_sz_2390_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v_b_2392_);
lean_ctor_set(v___x_2396_, 1, v___y_2394_);
return v___x_2396_;
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v_snd_2400_; lean_object* v___x_2401_; size_t v___x_2402_; size_t v___x_2403_; 
v_a_2397_ = lean_array_uget_borrowed(v_as_2389_, v_i_2391_);
v___x_2398_ = lean_unsigned_to_nat(0u);
v___x_2399_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2398_, v_a_2397_, v___y_2393_, v___y_2394_);
v_snd_2400_ = lean_ctor_get(v___x_2399_, 1);
lean_inc(v_snd_2400_);
lean_dec_ref(v___x_2399_);
v___x_2401_ = lean_box(0);
v___x_2402_ = ((size_t)1ULL);
v___x_2403_ = lean_usize_add(v_i_2391_, v___x_2402_);
v_i_2391_ = v___x_2403_;
v_b_2392_ = v___x_2401_;
v___y_2394_ = v_snd_2400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3___boxed(lean_object* v_as_2405_, lean_object* v_sz_2406_, lean_object* v_i_2407_, lean_object* v_b_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
size_t v_sz_boxed_2411_; size_t v_i_boxed_2412_; lean_object* v_res_2413_; 
v_sz_boxed_2411_ = lean_unbox_usize(v_sz_2406_);
lean_dec(v_sz_2406_);
v_i_boxed_2412_ = lean_unbox_usize(v_i_2407_);
lean_dec(v_i_2407_);
v_res_2413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_as_2405_, v_sz_boxed_2411_, v_i_boxed_2412_, v_b_2408_, v___y_2409_, v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec_ref(v_as_2405_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(lean_object* v_text_2414_, size_t v_sz_2415_, size_t v___x_2416_, lean_object* v___x_2417_, lean_object* v_subsections_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2421_; lean_object* v_snd_2422_; size_t v_sz_2423_; lean_object* v___x_2424_; lean_object* v_snd_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_text_2414_, v_sz_2415_, v___x_2416_, v___x_2417_, v___y_2419_, v___y_2420_);
v_snd_2422_ = lean_ctor_get(v___x_2421_, 1);
lean_inc(v_snd_2422_);
lean_dec_ref(v___x_2421_);
v_sz_2423_ = lean_array_size(v_subsections_2418_);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_subsections_2418_, v_sz_2423_, v___x_2416_, v___x_2417_, v___y_2419_, v_snd_2422_);
v_snd_2425_ = lean_ctor_get(v___x_2424_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v___x_2424_, 0);
lean_dec(v_unused_2433_);
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_snd_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2417_);
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_snd_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed(lean_object* v_text_2434_, lean_object* v_sz_2435_, lean_object* v___x_2436_, lean_object* v___x_2437_, lean_object* v_subsections_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
size_t v_sz_boxed_2441_; size_t v___x_10664__boxed_2442_; lean_object* v_res_2443_; 
v_sz_boxed_2441_ = lean_unbox_usize(v_sz_2435_);
lean_dec(v_sz_2435_);
v___x_10664__boxed_2442_ = lean_unbox_usize(v___x_2436_);
lean_dec(v___x_2436_);
v_res_2443_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(v_text_2434_, v_sz_boxed_2441_, v___x_10664__boxed_2442_, v___x_2437_, v_subsections_2438_, v___y_2439_, v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec_ref(v_subsections_2438_);
lean_dec_ref(v_text_2434_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(lean_object* v_a_2446_){
_start:
{
lean_object* v_text_2447_; lean_object* v_subsections_2448_; lean_object* v___x_2449_; size_t v_sz_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___f_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_text_2447_ = lean_ctor_get(v_a_2446_, 0);
lean_inc_ref(v_text_2447_);
v_subsections_2448_ = lean_ctor_get(v_a_2446_, 1);
lean_inc_ref(v_subsections_2448_);
lean_dec_ref(v_a_2446_);
v___x_2449_ = lean_box(0);
v_sz_2450_ = lean_array_size(v_text_2447_);
v___x_2451_ = lean_box_usize(v_sz_2450_);
v___x_2452_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1));
v___f_2453_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2453_, 0, v_text_2447_);
lean_closure_set(v___f_2453_, 1, v___x_2451_);
lean_closure_set(v___f_2453_, 2, v___x_2452_);
lean_closure_set(v___f_2453_, 3, v___x_2449_);
lean_closure_set(v___f_2453_, 4, v_subsections_2448_);
v___x_2454_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11));
v___x_2455_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13);
v___x_2456_ = l_Lean_Doc_MarkdownM_run_x27(v___f_2453_, v___x_2454_, v___x_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(lean_object* v_p_2457_, lean_object* v_level_2458_, lean_object* v_part_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2458_, v_part_2459_, v_a_2460_, v_a_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___boxed(lean_object* v_p_2463_, lean_object* v_level_2464_, lean_object* v_part_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(v_p_2463_, v_level_2464_, v_part_2465_, v_a_2466_, v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec_ref(v_part_2465_);
lean_dec(v_level_2464_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(lean_object* v_p_2469_, lean_object* v___x_2470_, lean_object* v_as_2471_, size_t v_sz_2472_, size_t v_i_2473_, lean_object* v_b_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2470_, v_as_2471_, v_sz_2472_, v_i_2473_, v_b_2474_, v___y_2475_, v___y_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___boxed(lean_object* v_p_2478_, lean_object* v___x_2479_, lean_object* v_as_2480_, lean_object* v_sz_2481_, lean_object* v_i_2482_, lean_object* v_b_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
size_t v_sz_boxed_2486_; size_t v_i_boxed_2487_; lean_object* v_res_2488_; 
v_sz_boxed_2486_ = lean_unbox_usize(v_sz_2481_);
lean_dec(v_sz_2481_);
v_i_boxed_2487_ = lean_unbox_usize(v_i_2482_);
lean_dec(v_i_2482_);
v_res_2488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(v_p_2478_, v___x_2479_, v_as_2480_, v_sz_boxed_2486_, v_i_boxed_2487_, v_b_2483_, v___y_2484_, v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec_ref(v_as_2480_);
lean_dec(v___x_2479_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(lean_object* v_s_2489_, lean_object* v_pattern_2490_, lean_object* v_replacement_2491_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v_s_2489_, v_replacement_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___boxed(lean_object* v_s_2493_, lean_object* v_pattern_2494_, lean_object* v_replacement_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(v_s_2493_, v_pattern_2494_, v_replacement_2495_);
lean_dec_ref(v_replacement_2495_);
lean_dec_ref(v_pattern_2494_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(lean_object* v_s_2497_, lean_object* v_replacement_2498_, lean_object* v_inst_2499_, lean_object* v_R_2500_, lean_object* v_a_2501_, lean_object* v_b_2502_, lean_object* v_c_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_2497_, v_replacement_2498_, v_a_2501_, v_b_2502_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_s_2505_, lean_object* v_replacement_2506_, lean_object* v_inst_2507_, lean_object* v_R_2508_, lean_object* v_a_2509_, lean_object* v_b_2510_, lean_object* v_c_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(v_s_2505_, v_replacement_2506_, v_inst_2507_, v_R_2508_, v_a_2509_, v_b_2510_, v_c_2511_);
lean_dec_ref(v_replacement_2506_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_2513_, lean_object* v_declName_2514_, uint8_t v_includeBuiltin_2515_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_findInternalDocString_x3f(v_env_2513_, v_declName_2514_, v_includeBuiltin_2515_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2546_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2546_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2546_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
if (lean_obj_tag(v_a_2518_) == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = lean_box(0);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2522_);
v___x_2524_ = v___x_2520_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
else
{
lean_object* v_val_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2545_; 
v_val_2526_ = lean_ctor_get(v_a_2518_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_a_2518_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2528_ = v_a_2518_;
v_isShared_2529_ = v_isSharedCheck_2545_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_val_2526_);
lean_dec(v_a_2518_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2545_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
if (lean_obj_tag(v_val_2526_) == 0)
{
lean_object* v_val_2530_; lean_object* v___x_2532_; 
v_val_2530_ = lean_ctor_get(v_val_2526_, 0);
lean_inc(v_val_2530_);
lean_dec_ref(v_val_2526_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v_val_2530_);
v___x_2532_ = v___x_2528_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_val_2530_);
v___x_2532_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2534_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2532_);
v___x_2534_ = v___x_2520_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
else
{
lean_object* v_val_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
v_val_2537_ = lean_ctor_get(v_val_2526_, 0);
lean_inc(v_val_2537_);
lean_dec_ref(v_val_2526_);
v___x_2538_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(v_val_2537_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2538_);
v___x_2540_ = v___x_2528_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2542_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2540_);
v___x_2542_ = v___x_2520_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
v_a_2547_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2517_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2517_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_2555_, lean_object* v_declName_2556_, lean_object* v_includeBuiltin_2557_, lean_object* v_a_2558_){
_start:
{
uint8_t v_includeBuiltin_boxed_2559_; lean_object* v_res_2560_; 
v_includeBuiltin_boxed_2559_ = lean_unbox(v_includeBuiltin_2557_);
v_res_2560_ = l_Lean_findSimpleDocString_x3f(v_env_2555_, v_declName_2556_, v_includeBuiltin_boxed_2559_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object* v_x_2563_, lean_object* v_x_2564_, lean_object* v_es_2565_, uint8_t v_level_2566_){
_start:
{
uint8_t v___x_2567_; uint8_t v___x_2568_; 
v___x_2567_ = 1;
v___x_2568_ = l_Lean_instOrdOLeanLevel_ord(v_level_2566_, v___x_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
lean_dec(v_es_2565_);
v___x_2569_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_));
return v___x_2569_;
}
else
{
lean_object* v___x_2570_; 
v___x_2570_ = lean_array_mk(v_es_2565_);
return v___x_2570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object* v_x_2571_, lean_object* v_x_2572_, lean_object* v_es_2573_, lean_object* v_level_2574_){
_start:
{
uint8_t v_level_boxed_2575_; lean_object* v_res_2576_; 
v_level_boxed_2575_ = lean_unbox(v_level_2574_);
v_res_2576_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(v_x_2571_, v_x_2572_, v_es_2573_, v_level_boxed_2575_);
lean_dec_ref(v_x_2572_);
lean_dec_ref(v_x_2571_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object* v_es_2577_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_array_mk(v_es_2577_);
return v___x_2578_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = lean_unsigned_to_nat(32u);
v___x_2580_ = lean_mk_empty_array_with_capacity(v___x_2579_);
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object* v___x_2582_, lean_object* v_x_2583_){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v___x_2584_ = lean_unsigned_to_nat(32u);
v___x_2585_ = lean_mk_empty_array_with_capacity(v___x_2584_);
v___x_2586_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_);
v___x_2587_ = ((size_t)5ULL);
lean_inc(v___x_2582_);
v___x_2588_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set(v___x_2588_, 1, v___x_2585_);
lean_ctor_set(v___x_2588_, 2, v___x_2582_);
lean_ctor_set(v___x_2588_, 3, v___x_2582_);
lean_ctor_set_usize(v___x_2588_, 4, v___x_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object* v___x_2589_, lean_object* v_x_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(v___x_2589_, v_x_2590_);
lean_dec_ref(v_x_2590_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_));
v___x_2613_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object* v_a_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_();
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object* v_env_2616_, lean_object* v_doc_2617_){
_start:
{
lean_object* v___x_2618_; lean_object* v_toEnvExtension_2619_; lean_object* v_asyncMode_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2618_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc_ref(v_toEnvExtension_2619_);
v_asyncMode_2620_ = lean_ctor_get(v_toEnvExtension_2619_, 2);
lean_inc(v_asyncMode_2620_);
lean_dec_ref(v_toEnvExtension_2619_);
v___x_2621_ = lean_box(0);
v___x_2622_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2618_, v_env_2616_, v_doc_2617_, v_asyncMode_2620_, v___x_2621_);
lean_dec(v_asyncMode_2620_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_getMainModuleDoc___closed__0(void){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object* v_env_2624_){
_start:
{
lean_object* v___x_2625_; lean_object* v_toEnvExtension_2626_; lean_object* v_asyncMode_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2625_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc_ref(v_toEnvExtension_2626_);
v_asyncMode_2627_ = lean_ctor_get(v_toEnvExtension_2626_, 2);
lean_inc(v_asyncMode_2627_);
lean_dec_ref(v_toEnvExtension_2626_);
v___x_2628_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2629_ = lean_box(0);
v___x_2630_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2628_, v___x_2625_, v_env_2624_, v_asyncMode_2627_, v___x_2629_);
lean_dec(v_asyncMode_2627_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_getModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v___x_2631_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object* v_env_2634_, lean_object* v_moduleName_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_Environment_getModuleIdx_x3f(v_env_2634_, v_moduleName_2635_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v___x_2637_; 
v___x_2637_ = lean_box(0);
return v___x_2637_;
}
else
{
lean_object* v_val_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2649_; 
v_val_2638_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2640_ = v___x_2636_;
v_isShared_2641_ = v_isSharedCheck_2649_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_val_2638_);
lean_dec(v___x_2636_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2649_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2642_ = lean_obj_once(&l_Lean_getModuleDoc_x3f___closed__0, &l_Lean_getModuleDoc_x3f___closed__0_once, _init_l_Lean_getModuleDoc_x3f___closed__0);
v___x_2643_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v___x_2644_ = 1;
v___x_2645_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2642_, v___x_2643_, v_env_2634_, v_val_2638_, v___x_2644_);
lean_dec(v_val_2638_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2645_);
v___x_2647_ = v___x_2640_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object* v_env_2650_, lean_object* v_moduleName_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_getModuleDoc_x3f(v_env_2650_, v_moduleName_2651_);
lean_dec(v_moduleName_2651_);
lean_dec_ref(v_env_2650_);
return v_res_2652_;
}
}
static lean_object* _init_l_Lean_getDocStringText___redArg___closed__1(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__0));
v___x_2655_ = l_Lean_stringToMessageData(v___x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object* v_inst_2659_, lean_object* v_inst_2660_, lean_object* v_stx_2661_){
_start:
{
lean_object* v_toApplicative_2668_; lean_object* v_toPure_2669_; lean_object* v_val_2671_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v_toApplicative_2668_ = lean_ctor_get(v_inst_2659_, 0);
v_toPure_2669_ = lean_ctor_get(v_toApplicative_2668_, 1);
v___x_2678_ = lean_unsigned_to_nat(1u);
v___x_2679_ = l_Lean_Syntax_getArg(v_stx_2661_, v___x_2678_);
switch(lean_obj_tag(v___x_2679_))
{
case 2:
{
lean_object* v_val_2680_; 
lean_inc(v_toPure_2669_);
lean_dec(v_stx_2661_);
lean_dec_ref(v_inst_2660_);
lean_dec_ref(v_inst_2659_);
v_val_2680_ = lean_ctor_get(v___x_2679_, 1);
lean_inc_ref(v_val_2680_);
lean_dec_ref(v___x_2679_);
v_val_2671_ = v_val_2680_;
goto v___jp_2670_;
}
case 1:
{
lean_object* v_kind_2681_; 
v_kind_2681_ = lean_ctor_get(v___x_2679_, 1);
lean_inc(v_kind_2681_);
if (lean_obj_tag(v_kind_2681_) == 1)
{
lean_object* v_pre_2682_; 
v_pre_2682_ = lean_ctor_get(v_kind_2681_, 0);
lean_inc(v_pre_2682_);
if (lean_obj_tag(v_pre_2682_) == 1)
{
lean_object* v_pre_2683_; 
v_pre_2683_ = lean_ctor_get(v_pre_2682_, 0);
lean_inc(v_pre_2683_);
if (lean_obj_tag(v_pre_2683_) == 1)
{
lean_object* v_pre_2684_; 
v_pre_2684_ = lean_ctor_get(v_pre_2683_, 0);
lean_inc(v_pre_2684_);
if (lean_obj_tag(v_pre_2684_) == 1)
{
lean_object* v_pre_2685_; 
v_pre_2685_ = lean_ctor_get(v_pre_2684_, 0);
if (lean_obj_tag(v_pre_2685_) == 0)
{
lean_object* v_str_2686_; lean_object* v_str_2687_; lean_object* v_str_2688_; lean_object* v_str_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v_str_2686_ = lean_ctor_get(v_kind_2681_, 1);
lean_inc_ref(v_str_2686_);
lean_dec_ref(v_kind_2681_);
v_str_2687_ = lean_ctor_get(v_pre_2682_, 1);
lean_inc_ref(v_str_2687_);
lean_dec_ref(v_pre_2682_);
v_str_2688_ = lean_ctor_get(v_pre_2683_, 1);
lean_inc_ref(v_str_2688_);
lean_dec_ref(v_pre_2683_);
v_str_2689_ = lean_ctor_get(v_pre_2684_, 1);
lean_inc_ref(v_str_2689_);
lean_dec_ref(v_pre_2684_);
v___x_2690_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_2691_ = lean_string_dec_eq(v_str_2689_, v___x_2690_);
lean_dec_ref(v_str_2689_);
if (v___x_2691_ == 0)
{
lean_dec_ref(v_str_2688_);
lean_dec_ref(v_str_2687_);
lean_dec_ref(v_str_2686_);
lean_dec_ref(v___x_2679_);
goto v___jp_2662_;
}
else
{
lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__2));
v___x_2693_ = lean_string_dec_eq(v_str_2688_, v___x_2692_);
lean_dec_ref(v_str_2688_);
if (v___x_2693_ == 0)
{
lean_dec_ref(v_str_2687_);
lean_dec_ref(v_str_2686_);
lean_dec_ref(v___x_2679_);
goto v___jp_2662_;
}
else
{
lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2694_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__3));
v___x_2695_ = lean_string_dec_eq(v_str_2687_, v___x_2694_);
lean_dec_ref(v_str_2687_);
if (v___x_2695_ == 0)
{
lean_dec_ref(v_str_2686_);
lean_dec_ref(v___x_2679_);
goto v___jp_2662_;
}
else
{
lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2696_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__4));
v___x_2697_ = lean_string_dec_eq(v_str_2686_, v___x_2696_);
lean_dec_ref(v_str_2686_);
if (v___x_2697_ == 0)
{
lean_dec_ref(v___x_2679_);
goto v___jp_2662_;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_unsigned_to_nat(0u);
v___x_2699_ = l_Lean_Syntax_getArg(v___x_2679_, v___x_2698_);
lean_dec_ref(v___x_2679_);
if (lean_obj_tag(v___x_2699_) == 2)
{
lean_object* v_val_2700_; 
lean_inc(v_toPure_2669_);
lean_dec(v_stx_2661_);
lean_dec_ref(v_inst_2660_);
lean_dec_ref(v_inst_2659_);
v_val_2700_ = lean_ctor_get(v___x_2699_, 1);
lean_inc_ref(v_val_2700_);
lean_dec_ref(v___x_2699_);
v_val_2671_ = v_val_2700_;
goto v___jp_2670_;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_dec(v___x_2699_);
v___x_2701_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2661_);
v___x_2702_ = l_Lean_MessageData_ofSyntax(v_stx_2661_);
v___x_2703_ = l_Lean_indentD(v___x_2702_);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2701_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = l_Lean_throwErrorAt___redArg(v_inst_2659_, v_inst_2660_, v_stx_2661_, v___x_2704_);
return v___x_2705_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2684_);
lean_dec_ref(v_pre_2683_);
lean_dec_ref(v_pre_2682_);
lean_dec_ref(v_kind_2681_);
lean_dec_ref(v___x_2679_);
goto v___jp_2662_;
}
}
else
{
lean_dec(v_pre_2684_);
lean_dec_ref(v_pre_2683_);
lean_dec_ref(v_pre_2682_);
lean_dec_ref(v_kind_2681_);
lean_dec_ref(v___x_2679_);
goto v___jp_2662_;
}
}
else
{
lean_dec_ref(v_pre_2682_);
lean_dec(v_pre_2683_);
lean_dec_ref(v_kind_2681_);
lean_dec_ref(v___x_2679_);
goto v___jp_2662_;
}
}
else
{
lean_dec(v_pre_2682_);
lean_dec_ref(v_kind_2681_);
lean_dec_ref(v___x_2679_);
goto v___jp_2662_;
}
}
else
{
lean_dec_ref(v___x_2679_);
lean_dec(v_kind_2681_);
goto v___jp_2662_;
}
}
default: 
{
lean_dec(v___x_2679_);
goto v___jp_2662_;
}
}
v___jp_2662_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2663_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2661_);
v___x_2664_ = l_Lean_MessageData_ofSyntax(v_stx_2661_);
v___x_2665_ = l_Lean_indentD(v___x_2664_);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2663_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = l_Lean_throwErrorAt___redArg(v_inst_2659_, v_inst_2660_, v_stx_2661_, v___x_2666_);
return v___x_2667_;
}
v___jp_2670_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = lean_string_utf8_byte_size(v_val_2671_);
v___x_2674_ = lean_unsigned_to_nat(2u);
v___x_2675_ = lean_nat_sub(v___x_2673_, v___x_2674_);
v___x_2676_ = lean_string_utf8_extract(v_val_2671_, v___x_2672_, v___x_2675_);
lean_dec(v___x_2675_);
lean_dec_ref(v_val_2671_);
v___x_2677_ = lean_apply_2(v_toPure_2669_, lean_box(0), v___x_2676_);
return v___x_2677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object* v_m_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_stx_2709_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_getDocStringText___redArg(v_inst_2707_, v_inst_2708_, v_stx_2709_);
return v___x_2710_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2711_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_2712_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default___closed__0));
v___x_2713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
lean_ctor_set(v___x_2713_, 2, v___x_2711_);
return v___x_2713_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default(void){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_obj_once(&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0, &l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_once, _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0);
return v___x_2714_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet(void){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object* v_a_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = lean_nat_to_int(v_a_2716_);
return v___x_2717_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_unsigned_to_nat(2u);
v___x_2725_ = lean_nat_to_int(v___x_2724_);
return v___x_2725_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_nat_to_int(v___x_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object* v_x_2740_, lean_object* v_x_2741_, lean_object* v_x_2742_){
_start:
{
if (lean_obj_tag(v_x_2742_) == 0)
{
lean_dec(v_x_2740_);
return v_x_2741_;
}
else
{
lean_object* v_head_2743_; lean_object* v_tail_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2755_; 
v_head_2743_ = lean_ctor_get(v_x_2742_, 0);
v_tail_2744_ = lean_ctor_get(v_x_2742_, 1);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_x_2742_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2746_ = v_x_2742_;
v_isShared_2747_ = v_isSharedCheck_2755_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_tail_2744_);
lean_inc(v_head_2743_);
lean_dec(v_x_2742_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2755_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
lean_inc(v_x_2740_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set_tag(v___x_2746_, 5);
lean_ctor_set(v___x_2746_, 1, v_x_2740_);
lean_ctor_set(v___x_2746_, 0, v_x_2741_);
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_x_2741_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_x_2740_);
v___x_2749_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = lean_unsigned_to_nat(0u);
v___x_2751_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2743_, v___x_2750_);
v___x_2752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2749_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v_x_2741_ = v___x_2752_;
v_x_2742_ = v_tail_2744_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object* v_x_2756_, lean_object* v_x_2757_, lean_object* v_x_2758_){
_start:
{
if (lean_obj_tag(v_x_2758_) == 0)
{
lean_dec(v_x_2756_);
return v_x_2757_;
}
else
{
lean_object* v_head_2759_; lean_object* v_tail_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2771_; 
v_head_2759_ = lean_ctor_get(v_x_2758_, 0);
v_tail_2760_ = lean_ctor_get(v_x_2758_, 1);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_x_2758_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2762_ = v_x_2758_;
v_isShared_2763_ = v_isSharedCheck_2771_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_tail_2760_);
lean_inc(v_head_2759_);
lean_dec(v_x_2758_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2771_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
lean_inc(v_x_2756_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set_tag(v___x_2762_, 5);
lean_ctor_set(v___x_2762_, 1, v_x_2756_);
lean_ctor_set(v___x_2762_, 0, v_x_2757_);
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_x_2757_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_x_2756_);
v___x_2765_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2766_ = lean_unsigned_to_nat(0u);
v___x_2767_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2759_, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2765_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(v_x_2756_, v___x_2768_, v_tail_2760_);
return v___x_2769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2772_, lean_object* v_x_2773_){
_start:
{
if (lean_obj_tag(v_x_2772_) == 0)
{
lean_object* v___x_2774_; 
lean_dec(v_x_2773_);
v___x_2774_ = lean_box(0);
return v___x_2774_;
}
else
{
lean_object* v_tail_2775_; 
v_tail_2775_ = lean_ctor_get(v_x_2772_, 1);
if (lean_obj_tag(v_tail_2775_) == 0)
{
lean_object* v_head_2776_; lean_object* v___x_2777_; 
lean_dec(v_x_2773_);
v_head_2776_ = lean_ctor_get(v_x_2772_, 0);
lean_inc(v_head_2776_);
lean_dec_ref(v_x_2772_);
v___x_2777_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2776_);
return v___x_2777_;
}
else
{
lean_object* v_head_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_inc(v_tail_2775_);
v_head_2778_ = lean_ctor_get(v_x_2772_, 0);
lean_inc(v_head_2778_);
lean_dec_ref(v_x_2772_);
v___x_2779_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2778_);
v___x_2780_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(v_x_2773_, v___x_2779_, v_tail_2775_);
return v___x_2780_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0));
v___x_2783_ = lean_string_length(v___x_2782_);
return v___x_2783_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4);
v___x_2785_ = lean_nat_to_int(v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_xs_2793_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; 
v___x_2794_ = lean_array_get_size(v_xs_2793_);
v___x_2795_ = lean_unsigned_to_nat(0u);
v___x_2796_ = lean_nat_dec_eq(v___x_2794_, v___x_2795_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2797_ = lean_array_to_list(v_xs_2793_);
v___x_2798_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2799_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_2797_, v___x_2798_);
v___x_2800_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_2801_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_2802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
lean_ctor_set(v___x_2802_, 1, v___x_2799_);
v___x_2803_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2800_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = l_Std_Format_fill(v___x_2805_);
return v___x_2806_;
}
else
{
lean_object* v___x_2807_; 
lean_dec_ref(v_xs_2793_);
v___x_2807_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_2862_, lean_object* v_prec_2863_){
_start:
{
switch(lean_obj_tag(v_x_2862_))
{
case 0:
{
lean_object* v_string_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2884_; 
v_string_2864_ = lean_ctor_get(v_x_2862_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2866_ = v_x_2862_;
v_isShared_2867_ = v_isSharedCheck_2884_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_string_2864_);
lean_dec(v_x_2862_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2884_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___y_2869_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2880_ = lean_unsigned_to_nat(1024u);
v___x_2881_ = lean_nat_dec_le(v___x_2880_, v_prec_2863_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; 
v___x_2882_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2869_ = v___x_2882_;
goto v___jp_2868_;
}
else
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2869_ = v___x_2883_;
goto v___jp_2868_;
}
v___jp_2868_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2870_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_2871_ = l_String_quote(v_string_2864_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set_tag(v___x_2866_, 3);
lean_ctor_set(v___x_2866_, 0, v___x_2871_);
v___x_2873_ = v___x_2866_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2870_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
lean_inc(v___y_2869_);
v___x_2875_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___y_2869_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = 0;
v___x_2877_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set_uint8(v___x_2877_, sizeof(void*)*1, v___x_2876_);
v___x_2878_ = l_Repr_addAppParen(v___x_2877_, v_prec_2863_);
return v___x_2878_;
}
}
}
}
case 1:
{
lean_object* v_content_2885_; lean_object* v___y_2887_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v_content_2885_ = lean_ctor_get(v_x_2862_, 0);
lean_inc_ref(v_content_2885_);
lean_dec_ref(v_x_2862_);
v___x_2895_ = lean_unsigned_to_nat(1024u);
v___x_2896_ = lean_nat_dec_le(v___x_2895_, v_prec_2863_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2887_ = v___x_2897_;
goto v___jp_2886_;
}
else
{
lean_object* v___x_2898_; 
v___x_2898_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2887_ = v___x_2898_;
goto v___jp_2886_;
}
v___jp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2888_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7));
v___x_2889_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2885_);
v___x_2890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
lean_inc(v___y_2887_);
v___x_2891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___y_2887_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = 0;
v___x_2893_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set_uint8(v___x_2893_, sizeof(void*)*1, v___x_2892_);
v___x_2894_ = l_Repr_addAppParen(v___x_2893_, v_prec_2863_);
return v___x_2894_;
}
}
case 2:
{
lean_object* v_content_2899_; lean_object* v___y_2901_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v_content_2899_ = lean_ctor_get(v_x_2862_, 0);
lean_inc_ref(v_content_2899_);
lean_dec_ref(v_x_2862_);
v___x_2909_ = lean_unsigned_to_nat(1024u);
v___x_2910_ = lean_nat_dec_le(v___x_2909_, v_prec_2863_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2901_ = v___x_2911_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2912_; 
v___x_2912_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2901_ = v___x_2912_;
goto v___jp_2900_;
}
v___jp_2900_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2902_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10));
v___x_2903_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2899_);
v___x_2904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
lean_inc(v___y_2901_);
v___x_2905_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___y_2901_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = 0;
v___x_2907_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*1, v___x_2906_);
v___x_2908_ = l_Repr_addAppParen(v___x_2907_, v_prec_2863_);
return v___x_2908_;
}
}
case 3:
{
lean_object* v_string_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2933_; 
v_string_2913_ = lean_ctor_get(v_x_2862_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2915_ = v_x_2862_;
v_isShared_2916_ = v_isSharedCheck_2933_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_string_2913_);
lean_dec(v_x_2862_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2933_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___y_2918_; lean_object* v___x_2929_; uint8_t v___x_2930_; 
v___x_2929_ = lean_unsigned_to_nat(1024u);
v___x_2930_ = lean_nat_dec_le(v___x_2929_, v_prec_2863_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2918_ = v___x_2931_;
goto v___jp_2917_;
}
else
{
lean_object* v___x_2932_; 
v___x_2932_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2918_ = v___x_2932_;
goto v___jp_2917_;
}
v___jp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2919_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13));
v___x_2920_ = l_String_quote(v_string_2913_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v___x_2920_);
v___x_2922_ = v___x_2915_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2919_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
lean_inc(v___y_2918_);
v___x_2924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___y_2918_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = 0;
v___x_2926_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*1, v___x_2925_);
v___x_2927_ = l_Repr_addAppParen(v___x_2926_, v_prec_2863_);
return v___x_2927_;
}
}
}
}
case 4:
{
uint8_t v_mode_2934_; lean_object* v_string_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2960_; 
v_mode_2934_ = lean_ctor_get_uint8(v_x_2862_, sizeof(void*)*1);
v_string_2935_ = lean_ctor_get(v_x_2862_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2937_ = v_x_2862_;
v_isShared_2938_ = v_isSharedCheck_2960_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_string_2935_);
lean_dec(v_x_2862_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2960_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___y_2940_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2956_ = lean_unsigned_to_nat(1024u);
v___x_2957_ = lean_nat_dec_le(v___x_2956_, v_prec_2863_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; 
v___x_2958_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2940_ = v___x_2958_;
goto v___jp_2939_;
}
else
{
lean_object* v___x_2959_; 
v___x_2959_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2940_ = v___x_2959_;
goto v___jp_2939_;
}
v___jp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; lean_object* v___x_2953_; 
v___x_2941_ = lean_box(1);
v___x_2942_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16));
v___x_2943_ = lean_unsigned_to_nat(1024u);
v___x_2944_ = l_Lean_Doc_instReprMathMode_repr(v_mode_2934_, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2942_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
lean_ctor_set(v___x_2946_, 1, v___x_2941_);
v___x_2947_ = l_String_quote(v_string_2935_);
v___x_2948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2946_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
lean_inc(v___y_2940_);
v___x_2950_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___y_2940_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = 0;
if (v_isShared_2938_ == 0)
{
lean_ctor_set_tag(v___x_2937_, 6);
lean_ctor_set(v___x_2937_, 0, v___x_2950_);
v___x_2953_ = v___x_2937_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2950_);
v___x_2953_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2954_; 
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*1, v___x_2951_);
v___x_2954_ = l_Repr_addAppParen(v___x_2953_, v_prec_2863_);
return v___x_2954_;
}
}
}
}
case 5:
{
lean_object* v_string_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2981_; 
v_string_2961_ = lean_ctor_get(v_x_2862_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2963_ = v_x_2862_;
v_isShared_2964_ = v_isSharedCheck_2981_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_string_2961_);
lean_dec(v_x_2862_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2981_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___y_2966_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2977_ = lean_unsigned_to_nat(1024u);
v___x_2978_ = lean_nat_dec_le(v___x_2977_, v_prec_2863_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2966_ = v___x_2979_;
goto v___jp_2965_;
}
else
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2966_ = v___x_2980_;
goto v___jp_2965_;
}
v___jp_2965_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2970_; 
v___x_2967_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19));
v___x_2968_ = l_String_quote(v_string_2961_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 3);
lean_ctor_set(v___x_2963_, 0, v___x_2968_);
v___x_2970_ = v___x_2963_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2967_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
lean_inc(v___y_2966_);
v___x_2972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___y_2966_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = 0;
v___x_2974_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set_uint8(v___x_2974_, sizeof(void*)*1, v___x_2973_);
v___x_2975_ = l_Repr_addAppParen(v___x_2974_, v_prec_2863_);
return v___x_2975_;
}
}
}
}
case 6:
{
lean_object* v_content_2982_; lean_object* v_url_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3007_; 
v_content_2982_ = lean_ctor_get(v_x_2862_, 0);
v_url_2983_ = lean_ctor_get(v_x_2862_, 1);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2985_ = v_x_2862_;
v_isShared_2986_ = v_isSharedCheck_3007_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_url_2983_);
lean_inc(v_content_2982_);
lean_dec(v_x_2862_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3007_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___y_2988_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3003_ = lean_unsigned_to_nat(1024u);
v___x_3004_ = lean_nat_dec_le(v___x_3003_, v_prec_2863_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2988_ = v___x_3005_;
goto v___jp_2987_;
}
else
{
lean_object* v___x_3006_; 
v___x_3006_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2988_ = v___x_3006_;
goto v___jp_2987_;
}
v___jp_2987_:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2989_ = lean_box(1);
v___x_2990_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22));
v___x_2991_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2982_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set_tag(v___x_2985_, 5);
lean_ctor_set(v___x_2985_, 1, v___x_2991_);
lean_ctor_set(v___x_2985_, 0, v___x_2990_);
v___x_2993_ = v___x_2985_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2990_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
lean_ctor_set(v___x_2994_, 1, v___x_2989_);
v___x_2995_ = l_String_quote(v_url_2983_);
v___x_2996_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
v___x_2997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2994_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
lean_inc(v___y_2988_);
v___x_2998_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___y_2988_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = 0;
v___x_3000_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set_uint8(v___x_3000_, sizeof(void*)*1, v___x_2999_);
v___x_3001_ = l_Repr_addAppParen(v___x_3000_, v_prec_2863_);
return v___x_3001_;
}
}
}
}
case 7:
{
lean_object* v_name_3008_; lean_object* v_content_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3033_; 
v_name_3008_ = lean_ctor_get(v_x_2862_, 0);
v_content_3009_ = lean_ctor_get(v_x_2862_, 1);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3011_ = v_x_2862_;
v_isShared_3012_ = v_isSharedCheck_3033_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_content_3009_);
lean_inc(v_name_3008_);
lean_dec(v_x_2862_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3033_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___y_3014_; lean_object* v___x_3029_; uint8_t v___x_3030_; 
v___x_3029_ = lean_unsigned_to_nat(1024u);
v___x_3030_ = lean_nat_dec_le(v___x_3029_, v_prec_2863_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3014_ = v___x_3031_;
goto v___jp_3013_;
}
else
{
lean_object* v___x_3032_; 
v___x_3032_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3014_ = v___x_3032_;
goto v___jp_3013_;
}
v___jp_3013_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3015_ = lean_box(1);
v___x_3016_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25));
v___x_3017_ = l_String_quote(v_name_3008_);
v___x_3018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set_tag(v___x_3011_, 5);
lean_ctor_set(v___x_3011_, 1, v___x_3018_);
lean_ctor_set(v___x_3011_, 0, v___x_3016_);
v___x_3020_ = v___x_3011_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3016_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
lean_ctor_set(v___x_3021_, 1, v___x_3015_);
v___x_3022_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3009_);
v___x_3023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
lean_inc(v___y_3014_);
v___x_3024_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___y_3014_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = 0;
v___x_3026_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set_uint8(v___x_3026_, sizeof(void*)*1, v___x_3025_);
v___x_3027_ = l_Repr_addAppParen(v___x_3026_, v_prec_2863_);
return v___x_3027_;
}
}
}
}
case 8:
{
lean_object* v_alt_3034_; lean_object* v_url_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3060_; 
v_alt_3034_ = lean_ctor_get(v_x_2862_, 0);
v_url_3035_ = lean_ctor_get(v_x_2862_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3037_ = v_x_2862_;
v_isShared_3038_ = v_isSharedCheck_3060_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_url_3035_);
lean_inc(v_alt_3034_);
lean_dec(v_x_2862_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3060_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___y_3040_; lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3056_ = lean_unsigned_to_nat(1024u);
v___x_3057_ = lean_nat_dec_le(v___x_3056_, v_prec_2863_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3040_ = v___x_3058_;
goto v___jp_3039_;
}
else
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3040_ = v___x_3059_;
goto v___jp_3039_;
}
v___jp_3039_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3041_ = lean_box(1);
v___x_3042_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28));
v___x_3043_ = l_String_quote(v_alt_3034_);
v___x_3044_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set_tag(v___x_3037_, 5);
lean_ctor_set(v___x_3037_, 1, v___x_3044_);
lean_ctor_set(v___x_3037_, 0, v___x_3042_);
v___x_3046_ = v___x_3037_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3042_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v___x_3041_);
v___x_3048_ = l_String_quote(v_url_3035_);
v___x_3049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
v___x_3050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3047_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
lean_inc(v___y_3040_);
v___x_3051_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___y_3040_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = 0;
v___x_3053_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3053_, 0, v___x_3051_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*1, v___x_3052_);
v___x_3054_ = l_Repr_addAppParen(v___x_3053_, v_prec_2863_);
return v___x_3054_;
}
}
}
}
case 9:
{
lean_object* v_content_3061_; lean_object* v___y_3063_; lean_object* v___x_3071_; uint8_t v___x_3072_; 
v_content_3061_ = lean_ctor_get(v_x_2862_, 0);
lean_inc_ref(v_content_3061_);
lean_dec_ref(v_x_2862_);
v___x_3071_ = lean_unsigned_to_nat(1024u);
v___x_3072_ = lean_nat_dec_le(v___x_3071_, v_prec_2863_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; 
v___x_3073_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3063_ = v___x_3073_;
goto v___jp_3062_;
}
else
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3063_ = v___x_3074_;
goto v___jp_3062_;
}
v___jp_3062_:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3064_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31));
v___x_3065_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3061_);
v___x_3066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
lean_inc(v___y_3063_);
v___x_3067_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___y_3063_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = 0;
v___x_3069_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3069_, 0, v___x_3067_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*1, v___x_3068_);
v___x_3070_ = l_Repr_addAppParen(v___x_3069_, v_prec_2863_);
return v___x_3070_;
}
}
default: 
{
lean_object* v_container_3075_; lean_object* v_content_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3124_; 
v_container_3075_ = lean_ctor_get(v_x_2862_, 0);
v_content_3076_ = lean_ctor_get(v_x_2862_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3078_ = v_x_2862_;
v_isShared_3079_ = v_isSharedCheck_3124_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_content_3076_);
lean_inc(v_container_3075_);
lean_dec(v_x_2862_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3124_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___y_3081_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3120_ = lean_unsigned_to_nat(1024u);
v___x_3121_ = lean_nat_dec_le(v___x_3120_, v_prec_2863_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3081_ = v___x_3122_;
goto v___jp_3080_;
}
else
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3081_ = v___x_3123_;
goto v___jp_3080_;
}
v___jp_3080_:
{
lean_object* v_name_3082_; lean_object* v_val_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3119_; 
v_name_3082_ = lean_ctor_get(v_container_3075_, 0);
v_val_3083_ = lean_ctor_get(v_container_3075_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_container_3075_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3085_ = v_container_3075_;
v_isShared_3086_ = v_isSharedCheck_3119_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_val_3083_);
lean_inc(v_name_3082_);
lean_dec(v_container_3075_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3119_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3087_ = lean_box(1);
v___x_3088_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34));
v___x_3089_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3090_ = lean_unsigned_to_nat(0u);
v___x_3091_ = l_Lean_Name_reprPrec(v_name_3082_, v___x_3090_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set_tag(v___x_3085_, 5);
lean_ctor_set(v___x_3085_, 1, v___x_3091_);
lean_ctor_set(v___x_3085_, 0, v___x_3089_);
v___x_3093_ = v___x_3085_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3089_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3094_; uint8_t v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3094_ = l_Std_Format_nestD(v___x_3093_);
v___x_3095_ = 0;
v___x_3096_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3096_, 0, v___x_3094_);
lean_ctor_set_uint8(v___x_3096_, sizeof(void*)*1, v___x_3095_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set_tag(v___x_3078_, 5);
lean_ctor_set(v___x_3078_, 1, v___x_3087_);
lean_ctor_set(v___x_3078_, 0, v___x_3096_);
v___x_3098_ = v___x_3078_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v___x_3087_);
v___x_3098_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3099_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3100_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3083_);
lean_dec(v_val_3083_);
v___x_3101_ = l_Lean_Name_reprPrec(v___x_3100_, v___x_3090_);
v___x_3102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3099_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3102_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = l_Std_Format_nestD(v___x_3104_);
v___x_3106_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*1, v___x_3095_);
v___x_3107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3098_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = l_Std_Format_nestD(v___x_3107_);
v___x_3109_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
lean_ctor_set_uint8(v___x_3109_, sizeof(void*)*1, v___x_3095_);
v___x_3110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3088_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
lean_ctor_set(v___x_3111_, 1, v___x_3087_);
v___x_3112_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3076_);
v___x_3113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3111_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
lean_inc(v___y_3081_);
v___x_3114_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___y_3081_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
v___x_3115_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
lean_ctor_set_uint8(v___x_3115_, sizeof(void*)*1, v___x_3095_);
v___x_3116_ = l_Repr_addAppParen(v___x_3115_, v_prec_2863_);
return v___x_3116_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = lean_unsigned_to_nat(0u);
v___x_3127_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v___y_3125_, v___x_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_3128_, lean_object* v_prec_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_x_3128_, v_prec_3129_);
lean_dec(v_prec_3129_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object* v_xs_3131_){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3132_ = lean_array_get_size(v_xs_3131_);
v___x_3133_ = lean_unsigned_to_nat(0u);
v___x_3134_ = lean_nat_dec_eq(v___x_3132_, v___x_3133_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3135_ = lean_array_to_list(v_xs_3131_);
v___x_3136_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3137_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_3135_, v___x_3136_);
v___x_3138_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3139_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
lean_ctor_set(v___x_3140_, 1, v___x_3137_);
v___x_3141_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3138_);
lean_ctor_set(v___x_3143_, 1, v___x_3142_);
v___x_3144_ = l_Std_Format_fill(v___x_3143_);
return v___x_3144_;
}
else
{
lean_object* v___x_3145_; 
lean_dec_ref(v_xs_3131_);
v___x_3145_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3145_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_unsigned_to_nat(12u);
v___x_3177_ = lean_nat_to_int(v___x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object* v_x_3178_, lean_object* v_x_3179_, lean_object* v_x_3180_){
_start:
{
if (lean_obj_tag(v_x_3180_) == 0)
{
lean_dec(v_x_3178_);
return v_x_3179_;
}
else
{
lean_object* v_head_3181_; lean_object* v_tail_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3193_; 
v_head_3181_ = lean_ctor_get(v_x_3180_, 0);
v_tail_3182_ = lean_ctor_get(v_x_3180_, 1);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_x_3180_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3184_ = v_x_3180_;
v_isShared_3185_ = v_isSharedCheck_3193_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_tail_3182_);
lean_inc(v_head_3181_);
lean_dec(v_x_3180_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3193_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
lean_inc(v_x_3178_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set_tag(v___x_3184_, 5);
lean_ctor_set(v___x_3184_, 1, v_x_3178_);
lean_ctor_set(v___x_3184_, 0, v_x_3179_);
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_x_3179_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_x_3178_);
v___x_3187_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = lean_unsigned_to_nat(0u);
v___x_3189_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3181_, v___x_3188_);
v___x_3190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3187_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
v_x_3179_ = v___x_3190_;
v_x_3180_ = v_tail_3182_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object* v_x_3194_, lean_object* v_x_3195_, lean_object* v_x_3196_){
_start:
{
if (lean_obj_tag(v_x_3196_) == 0)
{
lean_dec(v_x_3194_);
return v_x_3195_;
}
else
{
lean_object* v_head_3197_; lean_object* v_tail_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3209_; 
v_head_3197_ = lean_ctor_get(v_x_3196_, 0);
v_tail_3198_ = lean_ctor_get(v_x_3196_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_x_3196_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3200_ = v_x_3196_;
v_isShared_3201_ = v_isSharedCheck_3209_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_tail_3198_);
lean_inc(v_head_3197_);
lean_dec(v_x_3196_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3209_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
lean_inc(v_x_3194_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set_tag(v___x_3200_, 5);
lean_ctor_set(v___x_3200_, 1, v_x_3194_);
lean_ctor_set(v___x_3200_, 0, v_x_3195_);
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_x_3195_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_x_3194_);
v___x_3203_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3204_ = lean_unsigned_to_nat(0u);
v___x_3205_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3197_, v___x_3204_);
v___x_3206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3203_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(v_x_3194_, v___x_3206_, v_tail_3198_);
return v___x_3207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object* v_x_3210_, lean_object* v_x_3211_){
_start:
{
if (lean_obj_tag(v_x_3210_) == 0)
{
lean_object* v___x_3212_; 
lean_dec(v_x_3211_);
v___x_3212_ = lean_box(0);
return v___x_3212_;
}
else
{
lean_object* v_tail_3213_; 
v_tail_3213_ = lean_ctor_get(v_x_3210_, 1);
if (lean_obj_tag(v_tail_3213_) == 0)
{
lean_object* v_head_3214_; lean_object* v___x_3215_; 
lean_dec(v_x_3211_);
v_head_3214_ = lean_ctor_get(v_x_3210_, 0);
lean_inc(v_head_3214_);
lean_dec_ref(v_x_3210_);
v___x_3215_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3214_);
return v___x_3215_;
}
else
{
lean_object* v_head_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
lean_inc(v_tail_3213_);
v_head_3216_ = lean_ctor_get(v_x_3210_, 0);
lean_inc(v_head_3216_);
lean_dec_ref(v_x_3210_);
v___x_3217_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3216_);
v___x_3218_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(v_x_3211_, v___x_3217_, v_tail_3213_);
return v___x_3218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object* v_xs_3219_){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3220_ = lean_array_get_size(v_xs_3219_);
v___x_3221_ = lean_unsigned_to_nat(0u);
v___x_3222_ = lean_nat_dec_eq(v___x_3220_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3223_ = lean_array_to_list(v_xs_3219_);
v___x_3224_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3225_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3223_, v___x_3224_);
v___x_3226_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3227_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v___x_3225_);
v___x_3229_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3228_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3226_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = l_Std_Format_fill(v___x_3231_);
return v___x_3232_;
}
else
{
lean_object* v___x_3233_; 
lean_dec_ref(v_xs_3219_);
v___x_3233_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3233_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_3236_ = lean_string_length(v___x_3235_);
return v___x_3236_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9);
v___x_3238_ = lean_nat_to_int(v___x_3237_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_x_3244_){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3245_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6));
v___x_3246_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3247_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_x_3244_);
v___x_3248_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = 0;
v___x_3250_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*1, v___x_3249_);
v___x_3251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3245_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3253_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
lean_ctor_set(v___x_3254_, 1, v___x_3251_);
v___x_3255_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3252_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set_uint8(v___x_3258_, sizeof(void*)*1, v___x_3249_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object* v_x_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_){
_start:
{
if (lean_obj_tag(v_x_3261_) == 0)
{
lean_dec(v_x_3259_);
return v_x_3260_;
}
else
{
lean_object* v_head_3262_; lean_object* v_tail_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3273_; 
v_head_3262_ = lean_ctor_get(v_x_3261_, 0);
v_tail_3263_ = lean_ctor_get(v_x_3261_, 1);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_x_3261_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3265_ = v_x_3261_;
v_isShared_3266_ = v_isSharedCheck_3273_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_tail_3263_);
lean_inc(v_head_3262_);
lean_dec(v_x_3261_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3273_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
lean_inc(v_x_3259_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set_tag(v___x_3265_, 5);
lean_ctor_set(v___x_3265_, 1, v_x_3259_);
lean_ctor_set(v___x_3265_, 0, v_x_3260_);
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_x_3260_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_x_3259_);
v___x_3268_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3262_);
v___x_3270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3268_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v_x_3260_ = v___x_3270_;
v_x_3261_ = v_tail_3263_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object* v_x_3274_, lean_object* v_x_3275_, lean_object* v_x_3276_){
_start:
{
if (lean_obj_tag(v_x_3276_) == 0)
{
lean_dec(v_x_3274_);
return v_x_3275_;
}
else
{
lean_object* v_head_3277_; lean_object* v_tail_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3288_; 
v_head_3277_ = lean_ctor_get(v_x_3276_, 0);
v_tail_3278_ = lean_ctor_get(v_x_3276_, 1);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_x_3276_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3280_ = v_x_3276_;
v_isShared_3281_ = v_isSharedCheck_3288_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_tail_3278_);
lean_inc(v_head_3277_);
lean_dec(v_x_3276_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3288_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
lean_inc(v_x_3274_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set_tag(v___x_3280_, 5);
lean_ctor_set(v___x_3280_, 1, v_x_3274_);
lean_ctor_set(v___x_3280_, 0, v_x_3275_);
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_x_3275_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_x_3274_);
v___x_3283_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3277_);
v___x_3285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(v_x_3274_, v___x_3285_, v_tail_3278_);
return v___x_3286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_3289_, lean_object* v_x_3290_){
_start:
{
if (lean_obj_tag(v_x_3289_) == 0)
{
lean_object* v___x_3291_; 
lean_dec(v_x_3290_);
v___x_3291_ = lean_box(0);
return v___x_3291_;
}
else
{
lean_object* v_tail_3292_; 
v_tail_3292_ = lean_ctor_get(v_x_3289_, 1);
if (lean_obj_tag(v_tail_3292_) == 0)
{
lean_object* v_head_3293_; lean_object* v___x_3294_; 
lean_dec(v_x_3290_);
v_head_3293_ = lean_ctor_get(v_x_3289_, 0);
lean_inc(v_head_3293_);
lean_dec_ref(v_x_3289_);
v___x_3294_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3293_);
return v___x_3294_;
}
else
{
lean_object* v_head_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
lean_inc(v_tail_3292_);
v_head_3295_ = lean_ctor_get(v_x_3289_, 0);
lean_inc(v_head_3295_);
lean_dec_ref(v_x_3289_);
v___x_3296_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3295_);
v___x_3297_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(v_x_3290_, v___x_3296_, v_tail_3292_);
return v___x_3297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object* v_xs_3298_){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; 
v___x_3299_ = lean_array_get_size(v_xs_3298_);
v___x_3300_ = lean_unsigned_to_nat(0u);
v___x_3301_ = lean_nat_dec_eq(v___x_3299_, v___x_3300_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3302_ = lean_array_to_list(v_xs_3298_);
v___x_3303_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3304_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(v___x_3302_, v___x_3303_);
v___x_3305_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3306_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
lean_ctor_set(v___x_3307_, 1, v___x_3304_);
v___x_3308_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3305_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = l_Std_Format_fill(v___x_3310_);
return v___x_3311_;
}
else
{
lean_object* v___x_3312_; 
lean_dec_ref(v_xs_3298_);
v___x_3312_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3312_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = lean_unsigned_to_nat(0u);
v___x_3320_ = lean_nat_to_int(v___x_3319_);
return v___x_3320_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = lean_unsigned_to_nat(8u);
v___x_3337_ = lean_nat_to_int(v___x_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_x_3341_){
_start:
{
lean_object* v_term_3342_; lean_object* v_desc_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3375_; 
v_term_3342_ = lean_ctor_get(v_x_3341_, 0);
v_desc_3343_ = lean_ctor_get(v_x_3341_, 1);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_x_3341_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3345_ = v_x_3341_;
v_isShared_3346_ = v_isSharedCheck_3375_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_desc_3343_);
lean_inc(v_term_3342_);
lean_dec(v_x_3341_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3375_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3352_; 
v___x_3347_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3348_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3));
v___x_3349_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3350_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_term_3342_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set_tag(v___x_3345_, 4);
lean_ctor_set(v___x_3345_, 1, v___x_3350_);
lean_ctor_set(v___x_3345_, 0, v___x_3349_);
v___x_3352_ = v___x_3345_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v___x_3350_);
v___x_3352_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
uint8_t v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3353_ = 0;
v___x_3354_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set_uint8(v___x_3354_, sizeof(void*)*1, v___x_3353_);
v___x_3355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3348_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = lean_box(1);
v___x_3359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6));
v___x_3361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3359_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
lean_ctor_set(v___x_3362_, 1, v___x_3347_);
v___x_3363_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_desc_3343_);
v___x_3364_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3349_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
lean_ctor_set_uint8(v___x_3365_, sizeof(void*)*1, v___x_3353_);
v___x_3366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3362_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3368_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3369_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
lean_ctor_set(v___x_3369_, 1, v___x_3366_);
v___x_3370_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3367_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
lean_ctor_set_uint8(v___x_3373_, sizeof(void*)*1, v___x_3353_);
return v___x_3373_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object* v_x_3376_, lean_object* v_x_3377_, lean_object* v_x_3378_){
_start:
{
if (lean_obj_tag(v_x_3378_) == 0)
{
lean_dec(v_x_3376_);
return v_x_3377_;
}
else
{
lean_object* v_head_3379_; lean_object* v_tail_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3390_; 
v_head_3379_ = lean_ctor_get(v_x_3378_, 0);
v_tail_3380_ = lean_ctor_get(v_x_3378_, 1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_x_3378_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3382_ = v_x_3378_;
v_isShared_3383_ = v_isSharedCheck_3390_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_tail_3380_);
lean_inc(v_head_3379_);
lean_dec(v_x_3378_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3390_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
lean_inc(v_x_3376_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set_tag(v___x_3382_, 5);
lean_ctor_set(v___x_3382_, 1, v_x_3376_);
lean_ctor_set(v___x_3382_, 0, v_x_3377_);
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_x_3377_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_x_3376_);
v___x_3385_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3379_);
v___x_3387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v_x_3377_ = v___x_3387_;
v_x_3378_ = v_tail_3380_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object* v_x_3391_, lean_object* v_x_3392_, lean_object* v_x_3393_){
_start:
{
if (lean_obj_tag(v_x_3393_) == 0)
{
lean_dec(v_x_3391_);
return v_x_3392_;
}
else
{
lean_object* v_head_3394_; lean_object* v_tail_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3405_; 
v_head_3394_ = lean_ctor_get(v_x_3393_, 0);
v_tail_3395_ = lean_ctor_get(v_x_3393_, 1);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_x_3393_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3397_ = v_x_3393_;
v_isShared_3398_ = v_isSharedCheck_3405_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_tail_3395_);
lean_inc(v_head_3394_);
lean_dec(v_x_3393_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3405_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
lean_inc(v_x_3391_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 5);
lean_ctor_set(v___x_3397_, 1, v_x_3391_);
lean_ctor_set(v___x_3397_, 0, v_x_3392_);
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_x_3392_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_x_3391_);
v___x_3400_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3394_);
v___x_3402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3400_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(v_x_3391_, v___x_3402_, v_tail_3395_);
return v___x_3403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object* v_x_3406_, lean_object* v_x_3407_){
_start:
{
if (lean_obj_tag(v_x_3406_) == 0)
{
lean_object* v___x_3408_; 
lean_dec(v_x_3407_);
v___x_3408_ = lean_box(0);
return v___x_3408_;
}
else
{
lean_object* v_tail_3409_; 
v_tail_3409_ = lean_ctor_get(v_x_3406_, 1);
if (lean_obj_tag(v_tail_3409_) == 0)
{
lean_object* v_head_3410_; lean_object* v___x_3411_; 
lean_dec(v_x_3407_);
v_head_3410_ = lean_ctor_get(v_x_3406_, 0);
lean_inc(v_head_3410_);
lean_dec_ref(v_x_3406_);
v___x_3411_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3410_);
return v___x_3411_;
}
else
{
lean_object* v_head_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_inc(v_tail_3409_);
v_head_3412_ = lean_ctor_get(v_x_3406_, 0);
lean_inc(v_head_3412_);
lean_dec_ref(v_x_3406_);
v___x_3413_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3412_);
v___x_3414_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(v_x_3407_, v___x_3413_, v_tail_3409_);
return v___x_3414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object* v_xs_3415_){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3416_ = lean_array_get_size(v_xs_3415_);
v___x_3417_ = lean_unsigned_to_nat(0u);
v___x_3418_ = lean_nat_dec_eq(v___x_3416_, v___x_3417_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3419_ = lean_array_to_list(v_xs_3415_);
v___x_3420_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3421_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(v___x_3419_, v___x_3420_);
v___x_3422_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3423_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
lean_ctor_set(v___x_3424_, 1, v___x_3421_);
v___x_3425_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3422_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Std_Format_fill(v___x_3427_);
return v___x_3428_;
}
else
{
lean_object* v___x_3429_; 
lean_dec_ref(v_xs_3415_);
v___x_3429_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object* v_x_3448_, lean_object* v_prec_3449_){
_start:
{
switch(lean_obj_tag(v_x_3448_))
{
case 0:
{
lean_object* v_contents_3450_; lean_object* v___y_3452_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
v_contents_3450_ = lean_ctor_get(v_x_3448_, 0);
lean_inc_ref(v_contents_3450_);
lean_dec_ref(v_x_3448_);
v___x_3460_ = lean_unsigned_to_nat(1024u);
v___x_3461_ = lean_nat_dec_le(v___x_3460_, v_prec_3449_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3452_ = v___x_3462_;
goto v___jp_3451_;
}
else
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3452_ = v___x_3463_;
goto v___jp_3451_;
}
v___jp_3451_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3453_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2));
v___x_3454_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_contents_3450_);
v___x_3455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3453_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
lean_inc(v___y_3452_);
v___x_3456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___y_3452_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = 0;
v___x_3458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set_uint8(v___x_3458_, sizeof(void*)*1, v___x_3457_);
v___x_3459_ = l_Repr_addAppParen(v___x_3458_, v_prec_3449_);
return v___x_3459_;
}
}
case 1:
{
lean_object* v_content_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3484_; 
v_content_3464_ = lean_ctor_get(v_x_3448_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_x_3448_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3466_ = v_x_3448_;
v_isShared_3467_ = v_isSharedCheck_3484_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_content_3464_);
lean_dec(v_x_3448_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3484_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___y_3469_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3480_ = lean_unsigned_to_nat(1024u);
v___x_3481_ = lean_nat_dec_le(v___x_3480_, v_prec_3449_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3469_ = v___x_3482_;
goto v___jp_3468_;
}
else
{
lean_object* v___x_3483_; 
v___x_3483_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3469_ = v___x_3483_;
goto v___jp_3468_;
}
v___jp_3468_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3470_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5));
v___x_3471_ = l_String_quote(v_content_3464_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set_tag(v___x_3466_, 3);
lean_ctor_set(v___x_3466_, 0, v___x_3471_);
v___x_3473_ = v___x_3466_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; uint8_t v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3470_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
lean_inc(v___y_3469_);
v___x_3475_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___y_3469_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = 0;
v___x_3477_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3477_, 0, v___x_3475_);
lean_ctor_set_uint8(v___x_3477_, sizeof(void*)*1, v___x_3476_);
v___x_3478_ = l_Repr_addAppParen(v___x_3477_, v_prec_3449_);
return v___x_3478_;
}
}
}
}
case 2:
{
lean_object* v_items_3485_; lean_object* v___y_3487_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v_items_3485_ = lean_ctor_get(v_x_3448_, 0);
lean_inc_ref(v_items_3485_);
lean_dec_ref(v_x_3448_);
v___x_3495_ = lean_unsigned_to_nat(1024u);
v___x_3496_ = lean_nat_dec_le(v___x_3495_, v_prec_3449_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3487_ = v___x_3497_;
goto v___jp_3486_;
}
else
{
lean_object* v___x_3498_; 
v___x_3498_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3487_ = v___x_3498_;
goto v___jp_3486_;
}
v___jp_3486_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3488_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8));
v___x_3489_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3485_);
v___x_3490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3488_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
lean_inc(v___y_3487_);
v___x_3491_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___y_3487_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = 0;
v___x_3493_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3493_, 0, v___x_3491_);
lean_ctor_set_uint8(v___x_3493_, sizeof(void*)*1, v___x_3492_);
v___x_3494_ = l_Repr_addAppParen(v___x_3493_, v_prec_3449_);
return v___x_3494_;
}
}
case 3:
{
lean_object* v_start_3499_; lean_object* v_items_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3535_; 
v_start_3499_ = lean_ctor_get(v_x_3448_, 0);
v_items_3500_ = lean_ctor_get(v_x_3448_, 1);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_x_3448_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3502_ = v_x_3448_;
v_isShared_3503_ = v_isSharedCheck_3535_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_items_3500_);
lean_inc(v_start_3499_);
lean_dec(v_x_3448_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3535_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3520_; lean_object* v___x_3531_; uint8_t v___x_3532_; 
v___x_3531_ = lean_unsigned_to_nat(1024u);
v___x_3532_ = lean_nat_dec_le(v___x_3531_, v_prec_3449_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; 
v___x_3533_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3520_ = v___x_3533_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3520_ = v___x_3534_;
goto v___jp_3519_;
}
v___jp_3504_:
{
lean_object* v___x_3510_; 
lean_inc(v___y_3506_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set_tag(v___x_3502_, 5);
lean_ctor_set(v___x_3502_, 1, v___y_3508_);
lean_ctor_set(v___x_3502_, 0, v___y_3506_);
v___x_3510_ = v___x_3502_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___y_3506_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v___y_3508_);
v___x_3510_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
lean_ctor_set(v___x_3511_, 1, v___y_3507_);
v___x_3512_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3500_);
v___x_3513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3511_);
lean_ctor_set(v___x_3513_, 1, v___x_3512_);
lean_inc(v___y_3505_);
v___x_3514_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___y_3505_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
v___x_3515_ = 0;
v___x_3516_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3516_, 0, v___x_3514_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*1, v___x_3515_);
v___x_3517_ = l_Repr_addAppParen(v___x_3516_, v_prec_3449_);
return v___x_3517_;
}
}
v___jp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v___x_3521_ = lean_box(1);
v___x_3522_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11));
v___x_3523_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12, &l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12);
v___x_3524_ = lean_int_dec_lt(v_start_3499_, v___x_3523_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = l_Int_repr(v_start_3499_);
lean_dec(v_start_3499_);
v___x_3526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
v___y_3505_ = v___y_3520_;
v___y_3506_ = v___x_3522_;
v___y_3507_ = v___x_3521_;
v___y_3508_ = v___x_3526_;
goto v___jp_3504_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3527_ = lean_unsigned_to_nat(1024u);
v___x_3528_ = l_Int_repr(v_start_3499_);
lean_dec(v_start_3499_);
v___x_3529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
v___x_3530_ = l_Repr_addAppParen(v___x_3529_, v___x_3527_);
v___y_3505_ = v___y_3520_;
v___y_3506_ = v___x_3522_;
v___y_3507_ = v___x_3521_;
v___y_3508_ = v___x_3530_;
goto v___jp_3504_;
}
}
}
}
case 4:
{
lean_object* v_items_3536_; lean_object* v___y_3538_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v_items_3536_ = lean_ctor_get(v_x_3448_, 0);
lean_inc_ref(v_items_3536_);
lean_dec_ref(v_x_3448_);
v___x_3546_ = lean_unsigned_to_nat(1024u);
v___x_3547_ = lean_nat_dec_le(v___x_3546_, v_prec_3449_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; 
v___x_3548_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3538_ = v___x_3548_;
goto v___jp_3537_;
}
else
{
lean_object* v___x_3549_; 
v___x_3549_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3538_ = v___x_3549_;
goto v___jp_3537_;
}
v___jp_3537_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3539_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15));
v___x_3540_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(v_items_3536_);
v___x_3541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3539_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
lean_inc(v___y_3538_);
v___x_3542_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___y_3538_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = 0;
v___x_3544_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3544_, 0, v___x_3542_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*1, v___x_3543_);
v___x_3545_ = l_Repr_addAppParen(v___x_3544_, v_prec_3449_);
return v___x_3545_;
}
}
case 5:
{
lean_object* v_items_3550_; lean_object* v___y_3552_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v_items_3550_ = lean_ctor_get(v_x_3448_, 0);
lean_inc_ref(v_items_3550_);
lean_dec_ref(v_x_3448_);
v___x_3560_ = lean_unsigned_to_nat(1024u);
v___x_3561_ = lean_nat_dec_le(v___x_3560_, v_prec_3449_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; 
v___x_3562_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3552_ = v___x_3562_;
goto v___jp_3551_;
}
else
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3552_ = v___x_3563_;
goto v___jp_3551_;
}
v___jp_3551_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; uint8_t v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3553_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18));
v___x_3554_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_items_3550_);
v___x_3555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3553_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
lean_inc(v___y_3552_);
v___x_3556_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___y_3552_);
lean_ctor_set(v___x_3556_, 1, v___x_3555_);
v___x_3557_ = 0;
v___x_3558_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3558_, 0, v___x_3556_);
lean_ctor_set_uint8(v___x_3558_, sizeof(void*)*1, v___x_3557_);
v___x_3559_ = l_Repr_addAppParen(v___x_3558_, v_prec_3449_);
return v___x_3559_;
}
}
case 6:
{
lean_object* v_content_3564_; lean_object* v___y_3566_; lean_object* v___x_3574_; uint8_t v___x_3575_; 
v_content_3564_ = lean_ctor_get(v_x_3448_, 0);
lean_inc_ref(v_content_3564_);
lean_dec_ref(v_x_3448_);
v___x_3574_ = lean_unsigned_to_nat(1024u);
v___x_3575_ = lean_nat_dec_le(v___x_3574_, v_prec_3449_);
if (v___x_3575_ == 0)
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3566_ = v___x_3576_;
goto v___jp_3565_;
}
else
{
lean_object* v___x_3577_; 
v___x_3577_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3566_ = v___x_3577_;
goto v___jp_3565_;
}
v___jp_3565_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3567_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21));
v___x_3568_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3564_);
v___x_3569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3567_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
lean_inc(v___y_3566_);
v___x_3570_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___y_3566_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = 0;
v___x_3572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3572_, 0, v___x_3570_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*1, v___x_3571_);
v___x_3573_ = l_Repr_addAppParen(v___x_3572_, v_prec_3449_);
return v___x_3573_;
}
}
default: 
{
lean_object* v_container_3578_; lean_object* v_content_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3627_; 
v_container_3578_ = lean_ctor_get(v_x_3448_, 0);
v_content_3579_ = lean_ctor_get(v_x_3448_, 1);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_x_3448_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3581_ = v_x_3448_;
v_isShared_3582_ = v_isSharedCheck_3627_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_content_3579_);
lean_inc(v_container_3578_);
lean_dec(v_x_3448_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3627_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___y_3584_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v___x_3623_ = lean_unsigned_to_nat(1024u);
v___x_3624_ = lean_nat_dec_le(v___x_3623_, v_prec_3449_);
if (v___x_3624_ == 0)
{
lean_object* v___x_3625_; 
v___x_3625_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3584_ = v___x_3625_;
goto v___jp_3583_;
}
else
{
lean_object* v___x_3626_; 
v___x_3626_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3584_ = v___x_3626_;
goto v___jp_3583_;
}
v___jp_3583_:
{
lean_object* v_name_3585_; lean_object* v_val_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3622_; 
v_name_3585_ = lean_ctor_get(v_container_3578_, 0);
v_val_3586_ = lean_ctor_get(v_container_3578_, 1);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_container_3578_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3588_ = v_container_3578_;
v_isShared_3589_ = v_isSharedCheck_3622_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_val_3586_);
lean_inc(v_name_3585_);
lean_dec(v_container_3578_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3622_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3590_ = lean_box(1);
v___x_3591_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24));
v___x_3592_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3593_ = lean_unsigned_to_nat(0u);
v___x_3594_ = l_Lean_Name_reprPrec(v_name_3585_, v___x_3593_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set_tag(v___x_3588_, 5);
lean_ctor_set(v___x_3588_, 1, v___x_3594_);
lean_ctor_set(v___x_3588_, 0, v___x_3592_);
v___x_3596_ = v___x_3588_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; uint8_t v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3597_ = l_Std_Format_nestD(v___x_3596_);
v___x_3598_ = 0;
v___x_3599_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*1, v___x_3598_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set_tag(v___x_3581_, 5);
lean_ctor_set(v___x_3581_, 1, v___x_3590_);
lean_ctor_set(v___x_3581_, 0, v___x_3599_);
v___x_3601_ = v___x_3581_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3599_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v___x_3590_);
v___x_3601_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3602_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3603_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3586_);
lean_dec(v_val_3586_);
v___x_3604_ = l_Lean_Name_reprPrec(v___x_3603_, v___x_3593_);
v___x_3605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3602_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = l_Std_Format_nestD(v___x_3607_);
v___x_3609_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
lean_ctor_set_uint8(v___x_3609_, sizeof(void*)*1, v___x_3598_);
v___x_3610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3601_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = l_Std_Format_nestD(v___x_3610_);
v___x_3612_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
lean_ctor_set_uint8(v___x_3612_, sizeof(void*)*1, v___x_3598_);
v___x_3613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3591_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
lean_ctor_set(v___x_3614_, 1, v___x_3590_);
v___x_3615_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3579_);
v___x_3616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3614_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
lean_inc(v___y_3584_);
v___x_3617_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___y_3584_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
lean_ctor_set_uint8(v___x_3618_, sizeof(void*)*1, v___x_3598_);
v___x_3619_ = l_Repr_addAppParen(v___x_3618_, v_prec_3449_);
return v___x_3619_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v___y_3628_, v___x_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object* v_x_3631_, lean_object* v_prec_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_x_3631_, v_prec_3632_);
lean_dec(v_prec_3632_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object* v_xs_3634_){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___x_3635_ = lean_array_get_size(v_xs_3634_);
v___x_3636_ = lean_unsigned_to_nat(0u);
v___x_3637_ = lean_nat_dec_eq(v___x_3635_, v___x_3636_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3638_ = lean_array_to_list(v_xs_3634_);
v___x_3639_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3640_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3638_, v___x_3639_);
v___x_3641_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3642_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
lean_ctor_set(v___x_3643_, 1, v___x_3640_);
v___x_3644_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3643_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3641_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = l_Std_Format_fill(v___x_3646_);
return v___x_3647_;
}
else
{
lean_object* v___x_3648_; 
lean_dec_ref(v_xs_3634_);
v___x_3648_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3648_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object* v_x_3652_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = ((lean_object*)(l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1));
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_x_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3654_);
lean_dec(v_x_3654_);
return v_res_3655_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = lean_unsigned_to_nat(9u);
v___x_3666_ = lean_nat_to_int(v___x_3665_);
return v___x_3666_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = lean_unsigned_to_nat(15u);
v___x_3671_ = lean_nat_to_int(v___x_3670_);
return v___x_3671_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = lean_unsigned_to_nat(11u);
v___x_3679_ = lean_nat_to_int(v___x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object* v_x_3683_, lean_object* v_x_3684_, lean_object* v_x_3685_){
_start:
{
if (lean_obj_tag(v_x_3685_) == 0)
{
lean_dec(v_x_3683_);
return v_x_3684_;
}
else
{
lean_object* v_head_3686_; lean_object* v_tail_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3697_; 
v_head_3686_ = lean_ctor_get(v_x_3685_, 0);
v_tail_3687_ = lean_ctor_get(v_x_3685_, 1);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_x_3685_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3689_ = v_x_3685_;
v_isShared_3690_ = v_isSharedCheck_3697_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_tail_3687_);
lean_inc(v_head_3686_);
lean_dec(v_x_3685_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3697_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
lean_inc(v_x_3683_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set_tag(v___x_3689_, 5);
lean_ctor_set(v___x_3689_, 1, v_x_3683_);
lean_ctor_set(v___x_3689_, 0, v_x_3684_);
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_x_3684_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_x_3683_);
v___x_3692_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3693_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3686_);
v___x_3694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(v_x_3683_, v___x_3694_, v_tail_3687_);
return v___x_3695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object* v_x_3698_, lean_object* v_x_3699_){
_start:
{
if (lean_obj_tag(v_x_3698_) == 0)
{
lean_object* v___x_3700_; 
lean_dec(v_x_3699_);
v___x_3700_ = lean_box(0);
return v___x_3700_;
}
else
{
lean_object* v_tail_3701_; 
v_tail_3701_ = lean_ctor_get(v_x_3698_, 1);
if (lean_obj_tag(v_tail_3701_) == 0)
{
lean_object* v_head_3702_; lean_object* v___x_3703_; 
lean_dec(v_x_3699_);
v_head_3702_ = lean_ctor_get(v_x_3698_, 0);
lean_inc(v_head_3702_);
lean_dec_ref(v_x_3698_);
v___x_3703_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3702_);
return v___x_3703_;
}
else
{
lean_object* v_head_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
lean_inc(v_tail_3701_);
v_head_3704_ = lean_ctor_get(v_x_3698_, 0);
lean_inc(v_head_3704_);
lean_dec_ref(v_x_3698_);
v___x_3705_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3704_);
v___x_3706_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(v_x_3699_, v___x_3705_, v_tail_3701_);
return v___x_3706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object* v_xs_3707_){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3708_ = lean_array_get_size(v_xs_3707_);
v___x_3709_ = lean_unsigned_to_nat(0u);
v___x_3710_ = lean_nat_dec_eq(v___x_3708_, v___x_3709_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3711_ = lean_array_to_list(v_xs_3707_);
v___x_3712_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3713_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(v___x_3711_, v___x_3712_);
v___x_3714_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3715_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
lean_ctor_set(v___x_3716_, 1, v___x_3713_);
v___x_3717_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3714_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = l_Std_Format_fill(v___x_3719_);
return v___x_3720_;
}
else
{
lean_object* v___x_3721_; 
lean_dec_ref(v_xs_3707_);
v___x_3721_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object* v_x_3722_){
_start:
{
lean_object* v_title_3723_; lean_object* v_titleString_3724_; lean_object* v_metadata_3725_; lean_object* v_content_3726_; lean_object* v_subParts_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; uint8_t v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v_title_3723_ = lean_ctor_get(v_x_3722_, 0);
lean_inc_ref(v_title_3723_);
v_titleString_3724_ = lean_ctor_get(v_x_3722_, 1);
lean_inc_ref(v_titleString_3724_);
v_metadata_3725_ = lean_ctor_get(v_x_3722_, 2);
lean_inc(v_metadata_3725_);
v_content_3726_ = lean_ctor_get(v_x_3722_, 3);
lean_inc_ref(v_content_3726_);
v_subParts_3727_ = lean_ctor_get(v_x_3722_, 4);
lean_inc_ref(v_subParts_3727_);
lean_dec_ref(v_x_3722_);
v___x_3728_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3729_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3));
v___x_3730_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4);
v___x_3731_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_title_3723_);
v___x_3732_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = 0;
v___x_3734_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set_uint8(v___x_3734_, sizeof(void*)*1, v___x_3733_);
v___x_3735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3729_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3735_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = lean_box(1);
v___x_3739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6));
v___x_3741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
lean_ctor_set(v___x_3742_, 1, v___x_3728_);
v___x_3743_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7);
v___x_3744_ = l_String_quote(v_titleString_3724_);
v___x_3745_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
v___x_3746_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3743_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*1, v___x_3733_);
v___x_3748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3742_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v___x_3736_);
v___x_3750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
lean_ctor_set(v___x_3750_, 1, v___x_3738_);
v___x_3751_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9));
v___x_3752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
lean_ctor_set(v___x_3753_, 1, v___x_3728_);
v___x_3754_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3755_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_metadata_3725_);
lean_dec(v_metadata_3725_);
v___x_3756_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3754_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set_uint8(v___x_3757_, sizeof(void*)*1, v___x_3733_);
v___x_3758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3753_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
lean_ctor_set(v___x_3759_, 1, v___x_3736_);
v___x_3760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
lean_ctor_set(v___x_3760_, 1, v___x_3738_);
v___x_3761_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11));
v___x_3762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
lean_ctor_set(v___x_3763_, 1, v___x_3728_);
v___x_3764_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12);
v___x_3765_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_content_3726_);
v___x_3766_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3764_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
lean_ctor_set_uint8(v___x_3767_, sizeof(void*)*1, v___x_3733_);
v___x_3768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3763_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
lean_ctor_set(v___x_3769_, 1, v___x_3736_);
v___x_3770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
lean_ctor_set(v___x_3770_, 1, v___x_3738_);
v___x_3771_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14));
v___x_3772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3770_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
lean_ctor_set(v___x_3773_, 1, v___x_3728_);
v___x_3774_ = l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(v_subParts_3727_);
v___x_3775_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3754_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
lean_ctor_set_uint8(v___x_3776_, sizeof(void*)*1, v___x_3733_);
v___x_3777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3773_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3779_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
lean_ctor_set(v___x_3780_, 1, v___x_3777_);
v___x_3781_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3780_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3778_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v___x_3784_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
lean_ctor_set_uint8(v___x_3784_, sizeof(void*)*1, v___x_3733_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object* v_x_3785_, lean_object* v_x_3786_, lean_object* v_x_3787_){
_start:
{
if (lean_obj_tag(v_x_3787_) == 0)
{
lean_dec(v_x_3785_);
return v_x_3786_;
}
else
{
lean_object* v_head_3788_; lean_object* v_tail_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3799_; 
v_head_3788_ = lean_ctor_get(v_x_3787_, 0);
v_tail_3789_ = lean_ctor_get(v_x_3787_, 1);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_x_3787_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3791_ = v_x_3787_;
v_isShared_3792_ = v_isSharedCheck_3799_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_tail_3789_);
lean_inc(v_head_3788_);
lean_dec(v_x_3787_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3799_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
lean_inc(v_x_3785_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set_tag(v___x_3791_, 5);
lean_ctor_set(v___x_3791_, 1, v_x_3785_);
lean_ctor_set(v___x_3791_, 0, v_x_3786_);
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_x_3786_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_x_3785_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3788_);
v___x_3796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3794_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
v_x_3786_ = v___x_3796_;
v_x_3787_ = v_tail_3789_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object* v_x_3800_, lean_object* v_x_3801_){
_start:
{
lean_object* v_fst_3802_; lean_object* v_snd_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3813_; 
v_fst_3802_ = lean_ctor_get(v_x_3800_, 0);
v_snd_3803_ = lean_ctor_get(v_x_3800_, 1);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_x_3800_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3805_ = v_x_3800_;
v_isShared_3806_ = v_isSharedCheck_3813_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_snd_3803_);
lean_inc(v_fst_3802_);
lean_dec(v_x_3800_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3813_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3807_ = l_Lean_instReprDeclarationRange_repr___redArg(v_fst_3802_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set_tag(v___x_3805_, 1);
lean_ctor_set(v___x_3805_, 1, v_x_3801_);
lean_ctor_set(v___x_3805_, 0, v___x_3807_);
v___x_3809_ = v___x_3805_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_x_3801_);
v___x_3809_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_snd_3803_);
v___x_3811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
lean_ctor_set(v___x_3811_, 1, v___x_3809_);
return v___x_3811_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object* v_x_3814_, lean_object* v_x_3815_, lean_object* v_x_3816_){
_start:
{
if (lean_obj_tag(v_x_3816_) == 0)
{
lean_dec(v_x_3814_);
return v_x_3815_;
}
else
{
lean_object* v_head_3817_; lean_object* v_tail_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3827_; 
v_head_3817_ = lean_ctor_get(v_x_3816_, 0);
v_tail_3818_ = lean_ctor_get(v_x_3816_, 1);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_x_3816_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3820_ = v_x_3816_;
v_isShared_3821_ = v_isSharedCheck_3827_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_tail_3818_);
lean_inc(v_head_3817_);
lean_dec(v_x_3816_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3827_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
lean_inc(v_x_3814_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set_tag(v___x_3820_, 5);
lean_ctor_set(v___x_3820_, 1, v_x_3814_);
lean_ctor_set(v___x_3820_, 0, v_x_3815_);
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_x_3815_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_x_3814_);
v___x_3823_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
lean_ctor_set(v___x_3824_, 1, v_head_3817_);
v_x_3815_ = v___x_3824_;
v_x_3816_ = v_tail_3818_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object* v_x_3828_, lean_object* v_x_3829_){
_start:
{
if (lean_obj_tag(v_x_3828_) == 0)
{
lean_object* v___x_3830_; 
lean_dec(v_x_3829_);
v___x_3830_ = lean_box(0);
return v___x_3830_;
}
else
{
lean_object* v_tail_3831_; 
v_tail_3831_ = lean_ctor_get(v_x_3828_, 1);
if (lean_obj_tag(v_tail_3831_) == 0)
{
lean_object* v_head_3832_; 
lean_dec(v_x_3829_);
v_head_3832_ = lean_ctor_get(v_x_3828_, 0);
lean_inc(v_head_3832_);
lean_dec_ref(v_x_3828_);
return v_head_3832_;
}
else
{
lean_object* v_head_3833_; lean_object* v___x_3834_; 
lean_inc(v_tail_3831_);
v_head_3833_ = lean_ctor_get(v_x_3828_, 0);
lean_inc(v_head_3833_);
lean_dec_ref(v_x_3828_);
v___x_3834_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(v_x_3829_, v_head_3833_, v_tail_3831_);
return v___x_3834_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0));
v___x_3837_ = lean_string_length(v___x_3836_);
return v___x_3837_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3838_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1);
v___x_3839_ = lean_nat_to_int(v___x_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object* v_x_3844_){
_start:
{
lean_object* v_fst_3845_; lean_object* v_snd_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3868_; 
v_fst_3845_ = lean_ctor_get(v_x_3844_, 0);
v_snd_3846_ = lean_ctor_get(v_x_3844_, 1);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_x_3844_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3848_ = v_x_3844_;
v_isShared_3849_ = v_isSharedCheck_3868_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_snd_3846_);
lean_inc(v_fst_3845_);
lean_dec(v_x_3844_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3868_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3850_ = l_Nat_reprFast(v_fst_3845_);
v___x_3851_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
v___x_3852_ = lean_box(0);
if (v_isShared_3849_ == 0)
{
lean_ctor_set_tag(v___x_3848_, 1);
lean_ctor_set(v___x_3848_, 1, v___x_3852_);
lean_ctor_set(v___x_3848_, 0, v___x_3851_);
v___x_3854_ = v___x_3848_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; uint8_t v___x_3865_; lean_object* v___x_3866_; 
v___x_3855_ = l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(v_snd_3846_, v___x_3854_);
v___x_3856_ = l_List_reverse___redArg(v___x_3855_);
v___x_3857_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3858_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(v___x_3856_, v___x_3857_);
v___x_3859_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2);
v___x_3860_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3));
v___x_3861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
lean_ctor_set(v___x_3861_, 1, v___x_3858_);
v___x_3862_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4));
v___x_3863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3861_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
v___x_3864_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3859_);
lean_ctor_set(v___x_3864_, 1, v___x_3863_);
v___x_3865_ = 0;
v___x_3866_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3866_, 0, v___x_3864_);
lean_ctor_set_uint8(v___x_3866_, sizeof(void*)*1, v___x_3865_);
return v___x_3866_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object* v_x_3869_, lean_object* v_x_3870_, lean_object* v_x_3871_){
_start:
{
if (lean_obj_tag(v_x_3871_) == 0)
{
lean_dec(v_x_3869_);
return v_x_3870_;
}
else
{
lean_object* v_head_3872_; lean_object* v_tail_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3883_; 
v_head_3872_ = lean_ctor_get(v_x_3871_, 0);
v_tail_3873_ = lean_ctor_get(v_x_3871_, 1);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_x_3871_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3875_ = v_x_3871_;
v_isShared_3876_ = v_isSharedCheck_3883_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_tail_3873_);
lean_inc(v_head_3872_);
lean_dec(v_x_3871_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3883_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
lean_inc(v_x_3869_);
if (v_isShared_3876_ == 0)
{
lean_ctor_set_tag(v___x_3875_, 5);
lean_ctor_set(v___x_3875_, 1, v_x_3869_);
lean_ctor_set(v___x_3875_, 0, v_x_3870_);
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_x_3870_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_x_3869_);
v___x_3878_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3872_);
v___x_3880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3878_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
v_x_3870_ = v___x_3880_;
v_x_3871_ = v_tail_3873_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object* v_x_3884_, lean_object* v_x_3885_, lean_object* v_x_3886_){
_start:
{
if (lean_obj_tag(v_x_3886_) == 0)
{
lean_dec(v_x_3884_);
return v_x_3885_;
}
else
{
lean_object* v_head_3887_; lean_object* v_tail_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3898_; 
v_head_3887_ = lean_ctor_get(v_x_3886_, 0);
v_tail_3888_ = lean_ctor_get(v_x_3886_, 1);
v_isSharedCheck_3898_ = !lean_is_exclusive(v_x_3886_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3890_ = v_x_3886_;
v_isShared_3891_ = v_isSharedCheck_3898_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_tail_3888_);
lean_inc(v_head_3887_);
lean_dec(v_x_3886_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3898_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
lean_inc(v_x_3884_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set_tag(v___x_3890_, 5);
lean_ctor_set(v___x_3890_, 1, v_x_3884_);
lean_ctor_set(v___x_3890_, 0, v_x_3885_);
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_x_3885_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_x_3884_);
v___x_3893_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3887_);
v___x_3895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3893_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(v_x_3884_, v___x_3895_, v_tail_3888_);
return v___x_3896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object* v_x_3899_, lean_object* v_x_3900_){
_start:
{
if (lean_obj_tag(v_x_3899_) == 0)
{
lean_object* v___x_3901_; 
lean_dec(v_x_3900_);
v___x_3901_ = lean_box(0);
return v___x_3901_;
}
else
{
lean_object* v_tail_3902_; 
v_tail_3902_ = lean_ctor_get(v_x_3899_, 1);
if (lean_obj_tag(v_tail_3902_) == 0)
{
lean_object* v_head_3903_; lean_object* v___x_3904_; 
lean_dec(v_x_3900_);
v_head_3903_ = lean_ctor_get(v_x_3899_, 0);
lean_inc(v_head_3903_);
lean_dec_ref(v_x_3899_);
v___x_3904_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3903_);
return v___x_3904_;
}
else
{
lean_object* v_head_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
lean_inc(v_tail_3902_);
v_head_3905_ = lean_ctor_get(v_x_3899_, 0);
lean_inc(v_head_3905_);
lean_dec_ref(v_x_3899_);
v___x_3906_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3905_);
v___x_3907_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(v_x_3900_, v___x_3906_, v_tail_3902_);
return v___x_3907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object* v_xs_3908_){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; uint8_t v___x_3911_; 
v___x_3909_ = lean_array_get_size(v_xs_3908_);
v___x_3910_ = lean_unsigned_to_nat(0u);
v___x_3911_ = lean_nat_dec_eq(v___x_3909_, v___x_3910_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3912_ = lean_array_to_list(v_xs_3908_);
v___x_3913_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3914_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(v___x_3912_, v___x_3913_);
v___x_3915_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3916_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
lean_ctor_set(v___x_3917_, 1, v___x_3914_);
v___x_3918_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3917_);
lean_ctor_set(v___x_3919_, 1, v___x_3918_);
v___x_3920_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3915_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = l_Std_Format_fill(v___x_3920_);
return v___x_3921_;
}
else
{
lean_object* v___x_3922_; 
lean_dec_ref(v_xs_3908_);
v___x_3922_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3922_;
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = lean_unsigned_to_nat(20u);
v___x_3939_ = lean_nat_to_int(v___x_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object* v_x_3940_){
_start:
{
lean_object* v_text_3941_; lean_object* v_sections_3942_; lean_object* v_declarationRange_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v_text_3941_ = lean_ctor_get(v_x_3940_, 0);
lean_inc_ref(v_text_3941_);
v_sections_3942_ = lean_ctor_get(v_x_3940_, 1);
lean_inc_ref(v_sections_3942_);
v_declarationRange_3943_ = lean_ctor_get(v_x_3940_, 2);
lean_inc_ref(v_declarationRange_3943_);
lean_dec_ref(v_x_3940_);
v___x_3944_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3945_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3));
v___x_3946_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3947_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_text_3941_);
v___x_3948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3946_);
lean_ctor_set(v___x_3948_, 1, v___x_3947_);
v___x_3949_ = 0;
v___x_3950_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
lean_ctor_set_uint8(v___x_3950_, sizeof(void*)*1, v___x_3949_);
v___x_3951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3945_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3951_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = lean_box(1);
v___x_3955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3953_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
v___x_3956_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5));
v___x_3957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3955_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
lean_ctor_set(v___x_3958_, 1, v___x_3944_);
v___x_3959_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3960_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(v_sections_3942_);
v___x_3961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set_uint8(v___x_3962_, sizeof(void*)*1, v___x_3949_);
v___x_3963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3958_);
lean_ctor_set(v___x_3963_, 1, v___x_3962_);
v___x_3964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
lean_ctor_set(v___x_3964_, 1, v___x_3952_);
v___x_3965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
lean_ctor_set(v___x_3965_, 1, v___x_3954_);
v___x_3966_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7));
v___x_3967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3965_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
lean_ctor_set(v___x_3968_, 1, v___x_3944_);
v___x_3969_ = lean_obj_once(&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8, &l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once, _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8);
v___x_3970_ = l_Lean_instReprDeclarationRange_repr___redArg(v_declarationRange_3943_);
v___x_3971_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3969_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
lean_ctor_set_uint8(v___x_3972_, sizeof(void*)*1, v___x_3949_);
v___x_3973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3968_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
v___x_3974_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3975_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
lean_ctor_set(v___x_3976_, 1, v___x_3973_);
v___x_3977_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3976_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
v___x_3979_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3974_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
lean_ctor_set_uint8(v___x_3980_, sizeof(void*)*1, v___x_3949_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object* v_x_3981_, lean_object* v_prec_3982_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(v_x_3981_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object* v_x_3984_, lean_object* v_prec_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l_Lean_VersoModuleDocs_instReprSnippet_repr(v_x_3984_, v_prec_3985_);
lean_dec(v_prec_3985_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object* v_x_3987_, lean_object* v_x_3988_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_x_3987_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object* v_x_3990_, lean_object* v_x_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(v_x_3990_, v_x_3991_);
lean_dec(v_x_3991_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_3993_, lean_object* v_prec_3994_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_x_3993_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_x_3996_, lean_object* v_prec_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(v_x_3996_, v_prec_3997_);
lean_dec(v_prec_3997_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object* v_x_3999_, lean_object* v_prec_4000_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_x_3999_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_x_4002_, lean_object* v_prec_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(v_x_4002_, v_prec_4003_);
lean_dec(v_prec_4003_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object* v_x_4005_, lean_object* v_x_4006_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_4005_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object* v_x_4008_, lean_object* v_x_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(v_x_4008_, v_x_4009_);
lean_dec(v_x_4009_);
lean_dec(v_x_4008_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object* v_x_4011_, lean_object* v_prec_4012_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_x_4011_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object* v_x_4014_, lean_object* v_prec_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(v_x_4014_, v_prec_4015_);
lean_dec(v_prec_4015_);
return v_res_4016_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object* v_level_4019_, lean_object* v_snippet_4020_){
_start:
{
lean_object* v_sections_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; uint8_t v___x_4024_; 
v_sections_4021_ = lean_ctor_get(v_snippet_4020_, 1);
v___x_4022_ = lean_unsigned_to_nat(0u);
v___x_4023_ = lean_array_get_size(v_sections_4021_);
v___x_4024_ = lean_nat_dec_lt(v___x_4022_, v___x_4023_);
if (v___x_4024_ == 0)
{
uint8_t v___x_4025_; 
v___x_4025_ = 1;
return v___x_4025_;
}
else
{
lean_object* v___x_4026_; lean_object* v_fst_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; uint8_t v___x_4030_; 
v___x_4026_ = lean_array_fget_borrowed(v_sections_4021_, v___x_4022_);
v_fst_4027_ = lean_ctor_get(v___x_4026_, 0);
v___x_4028_ = lean_unsigned_to_nat(1u);
v___x_4029_ = lean_nat_add(v_level_4019_, v___x_4028_);
v___x_4030_ = lean_nat_dec_le(v_fst_4027_, v___x_4029_);
lean_dec(v___x_4029_);
return v___x_4030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object* v_level_4031_, lean_object* v_snippet_4032_){
_start:
{
uint8_t v_res_4033_; lean_object* v_r_4034_; 
v_res_4033_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_4031_, v_snippet_4032_);
lean_dec_ref(v_snippet_4032_);
lean_dec(v_level_4031_);
v_r_4034_ = lean_box(v_res_4033_);
return v_r_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object* v_snippet_4035_){
_start:
{
lean_object* v_sections_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; uint8_t v___x_4040_; 
v_sections_4036_ = lean_ctor_get(v_snippet_4035_, 1);
v___x_4037_ = lean_array_get_size(v_sections_4036_);
v___x_4038_ = lean_unsigned_to_nat(1u);
v___x_4039_ = lean_nat_sub(v___x_4037_, v___x_4038_);
v___x_4040_ = lean_nat_dec_lt(v___x_4039_, v___x_4037_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4041_; 
lean_dec(v___x_4039_);
v___x_4041_ = lean_box(0);
return v___x_4041_;
}
else
{
lean_object* v___x_4042_; lean_object* v_fst_4043_; lean_object* v___x_4044_; 
v___x_4042_ = lean_array_fget_borrowed(v_sections_4036_, v___x_4039_);
lean_dec(v___x_4039_);
v_fst_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_fst_4043_);
v___x_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4044_, 0, v_fst_4043_);
return v___x_4044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object* v_snippet_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4045_);
lean_dec_ref(v_snippet_4045_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object* v_snippet_4047_, lean_object* v_block_4048_){
_start:
{
lean_object* v_text_4049_; lean_object* v_sections_4050_; lean_object* v_declarationRange_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; uint8_t v___x_4054_; 
v_text_4049_ = lean_ctor_get(v_snippet_4047_, 0);
v_sections_4050_ = lean_ctor_get(v_snippet_4047_, 1);
v_declarationRange_4051_ = lean_ctor_get(v_snippet_4047_, 2);
v___x_4052_ = lean_array_get_size(v_sections_4050_);
v___x_4053_ = lean_unsigned_to_nat(0u);
v___x_4054_ = lean_nat_dec_eq(v___x_4052_, v___x_4053_);
if (v___x_4054_ == 0)
{
lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v___x_4055_ = lean_unsigned_to_nat(1u);
v___x_4056_ = lean_nat_sub(v___x_4052_, v___x_4055_);
v___x_4057_ = lean_nat_dec_lt(v___x_4056_, v___x_4052_);
if (v___x_4057_ == 0)
{
lean_dec(v___x_4056_);
lean_dec_ref(v_block_4048_);
return v_snippet_4047_;
}
else
{
lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4101_; 
lean_inc_ref(v_declarationRange_4051_);
lean_inc_ref(v_sections_4050_);
lean_inc_ref(v_text_4049_);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_snippet_4047_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; lean_object* v_unused_4103_; lean_object* v_unused_4104_; 
v_unused_4102_ = lean_ctor_get(v_snippet_4047_, 2);
lean_dec(v_unused_4102_);
v_unused_4103_ = lean_ctor_get(v_snippet_4047_, 1);
lean_dec(v_unused_4103_);
v_unused_4104_ = lean_ctor_get(v_snippet_4047_, 0);
lean_dec(v_unused_4104_);
v___x_4059_ = v_snippet_4047_;
v_isShared_4060_ = v_isSharedCheck_4101_;
goto v_resetjp_4058_;
}
else
{
lean_dec(v_snippet_4047_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4101_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v_v_4061_; lean_object* v_snd_4062_; lean_object* v_snd_4063_; lean_object* v_fst_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4099_; 
v_v_4061_ = lean_array_fget(v_sections_4050_, v___x_4056_);
v_snd_4062_ = lean_ctor_get(v_v_4061_, 1);
lean_inc(v_snd_4062_);
v_snd_4063_ = lean_ctor_get(v_snd_4062_, 1);
lean_inc(v_snd_4063_);
v_fst_4064_ = lean_ctor_get(v_v_4061_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v_v_4061_);
if (v_isSharedCheck_4099_ == 0)
{
lean_object* v_unused_4100_; 
v_unused_4100_ = lean_ctor_get(v_v_4061_, 1);
lean_dec(v_unused_4100_);
v___x_4066_ = v_v_4061_;
v_isShared_4067_ = v_isSharedCheck_4099_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_fst_4064_);
lean_dec(v_v_4061_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4099_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v_fst_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4097_; 
v_fst_4068_ = lean_ctor_get(v_snd_4062_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v_snd_4062_);
if (v_isSharedCheck_4097_ == 0)
{
lean_object* v_unused_4098_; 
v_unused_4098_ = lean_ctor_get(v_snd_4062_, 1);
lean_dec(v_unused_4098_);
v___x_4070_ = v_snd_4062_;
v_isShared_4071_ = v_isSharedCheck_4097_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_fst_4068_);
lean_dec(v_snd_4062_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4097_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v_title_4072_; lean_object* v_titleString_4073_; lean_object* v_metadata_4074_; lean_object* v_content_4075_; lean_object* v_subParts_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4096_; 
v_title_4072_ = lean_ctor_get(v_snd_4063_, 0);
v_titleString_4073_ = lean_ctor_get(v_snd_4063_, 1);
v_metadata_4074_ = lean_ctor_get(v_snd_4063_, 2);
v_content_4075_ = lean_ctor_get(v_snd_4063_, 3);
v_subParts_4076_ = lean_ctor_get(v_snd_4063_, 4);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_snd_4063_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4078_ = v_snd_4063_;
v_isShared_4079_ = v_isSharedCheck_4096_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_subParts_4076_);
lean_inc(v_content_4075_);
lean_inc(v_metadata_4074_);
lean_inc(v_titleString_4073_);
lean_inc(v_title_4072_);
lean_dec(v_snd_4063_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4096_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4080_; lean_object* v_xs_x27_4081_; lean_object* v___x_4082_; lean_object* v___x_4084_; 
v___x_4080_ = lean_box(0);
v_xs_x27_4081_ = lean_array_fset(v_sections_4050_, v___x_4056_, v___x_4080_);
v___x_4082_ = lean_array_push(v_content_4075_, v_block_4048_);
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 3, v___x_4082_);
v___x_4084_ = v___x_4078_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_title_4072_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_titleString_4073_);
lean_ctor_set(v_reuseFailAlloc_4095_, 2, v_metadata_4074_);
lean_ctor_set(v_reuseFailAlloc_4095_, 3, v___x_4082_);
lean_ctor_set(v_reuseFailAlloc_4095_, 4, v_subParts_4076_);
v___x_4084_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4086_; 
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 1, v___x_4084_);
v___x_4086_ = v___x_4070_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_fst_4068_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4084_);
v___x_4086_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
lean_object* v___x_4088_; 
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 1, v___x_4086_);
v___x_4088_ = v___x_4066_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_fst_4064_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4089_; lean_object* v___x_4091_; 
v___x_4089_ = lean_array_fset(v_xs_x27_4081_, v___x_4056_, v___x_4088_);
lean_dec(v___x_4056_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 1, v___x_4089_);
v___x_4091_ = v___x_4059_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_text_4049_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v___x_4089_);
lean_ctor_set(v_reuseFailAlloc_4092_, 2, v_declarationRange_4051_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
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
lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4112_; 
lean_inc_ref(v_declarationRange_4051_);
lean_inc_ref(v_sections_4050_);
lean_inc_ref(v_text_4049_);
v_isSharedCheck_4112_ = !lean_is_exclusive(v_snippet_4047_);
if (v_isSharedCheck_4112_ == 0)
{
lean_object* v_unused_4113_; lean_object* v_unused_4114_; lean_object* v_unused_4115_; 
v_unused_4113_ = lean_ctor_get(v_snippet_4047_, 2);
lean_dec(v_unused_4113_);
v_unused_4114_ = lean_ctor_get(v_snippet_4047_, 1);
lean_dec(v_unused_4114_);
v_unused_4115_ = lean_ctor_get(v_snippet_4047_, 0);
lean_dec(v_unused_4115_);
v___x_4106_ = v_snippet_4047_;
v_isShared_4107_ = v_isSharedCheck_4112_;
goto v_resetjp_4105_;
}
else
{
lean_dec(v_snippet_4047_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4112_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4108_; lean_object* v___x_4110_; 
v___x_4108_ = lean_array_push(v_text_4049_, v_block_4048_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v___x_4108_);
v___x_4110_ = v___x_4106_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4108_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v_sections_4050_);
lean_ctor_set(v_reuseFailAlloc_4111_, 2, v_declarationRange_4051_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object* v_snippet_4116_, lean_object* v_level_4117_, lean_object* v_range_4118_, lean_object* v_part_4119_){
_start:
{
lean_object* v_text_4120_; lean_object* v_sections_4121_; lean_object* v_declarationRange_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4132_; 
v_text_4120_ = lean_ctor_get(v_snippet_4116_, 0);
v_sections_4121_ = lean_ctor_get(v_snippet_4116_, 1);
v_declarationRange_4122_ = lean_ctor_get(v_snippet_4116_, 2);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_snippet_4116_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4124_ = v_snippet_4116_;
v_isShared_4125_ = v_isSharedCheck_4132_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_declarationRange_4122_);
lean_inc(v_sections_4121_);
lean_inc(v_text_4120_);
lean_dec(v_snippet_4116_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4132_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4130_; 
v___x_4126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4126_, 0, v_range_4118_);
lean_ctor_set(v___x_4126_, 1, v_part_4119_);
v___x_4127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4127_, 0, v_level_4117_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = lean_array_push(v_sections_4121_, v___x_4127_);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 1, v___x_4128_);
v___x_4130_ = v___x_4124_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_text_4120_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v___x_4128_);
lean_ctor_set(v_reuseFailAlloc_4131_, 2, v_declarationRange_4122_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0(lean_object* v___x_4133_, lean_object* v___x_4134_, lean_object* v_x_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4133_, v___x_4134_, v___y_4136_, v___y_4137_, v___y_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_4140_, lean_object* v___x_4141_, lean_object* v_x_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_instToMarkdownSnippet___lam__0(v___x_4140_, v___x_4141_, v_x_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
lean_dec_ref(v___y_4144_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1(lean_object* v___x_4147_, lean_object* v___x_4148_, lean_object* v___x_4149_, lean_object* v_a_4150_, lean_object* v_x_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v___x_4155_; lean_object* v_snd_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4164_; 
v___x_4155_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4147_, v___x_4148_, v_a_4150_, v___y_4153_, v___y_4154_);
v_snd_4156_ = lean_ctor_get(v___x_4155_, 1);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4164_ == 0)
{
lean_object* v_unused_4165_; 
v_unused_4165_ = lean_ctor_get(v___x_4155_, 0);
lean_dec(v_unused_4165_);
v___x_4158_ = v___x_4155_;
v_isShared_4159_ = v_isSharedCheck_4164_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_snd_4156_);
lean_dec(v___x_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4164_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4160_; lean_object* v___x_4162_; 
v___x_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4149_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 0, v___x_4160_);
v___x_4162_ = v___x_4158_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4160_);
lean_ctor_set(v_reuseFailAlloc_4163_, 1, v_snd_4156_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_4166_, lean_object* v___x_4167_, lean_object* v___x_4168_, lean_object* v_a_4169_, lean_object* v_x_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_instToMarkdownSnippet___lam__1(v___x_4166_, v___x_4167_, v___x_4168_, v_a_4169_, v_x_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
lean_dec_ref(v___y_4172_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2(lean_object* v___x_4175_, lean_object* v___x_4176_, lean_object* v_a_4177_, lean_object* v_x_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v___x_4182_; lean_object* v_snd_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4191_; 
v___x_4182_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_box(0), v___x_4175_, v_a_4177_, v___y_4180_, v___y_4181_);
v_snd_4183_ = lean_ctor_get(v___x_4182_, 1);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4191_ == 0)
{
lean_object* v_unused_4192_; 
v_unused_4192_ = lean_ctor_get(v___x_4182_, 0);
lean_dec(v_unused_4192_);
v___x_4185_ = v___x_4182_;
v_isShared_4186_ = v_isSharedCheck_4191_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_snd_4183_);
lean_dec(v___x_4182_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4191_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4189_; 
v___x_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4176_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 0, v___x_4187_);
v___x_4189_ = v___x_4185_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4187_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v_snd_4183_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2___boxed(lean_object* v___x_4193_, lean_object* v___x_4194_, lean_object* v_a_4195_, lean_object* v_x_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Lean_instToMarkdownSnippet___lam__2(v___x_4193_, v___x_4194_, v_a_4195_, v_x_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
lean_dec_ref(v___y_4198_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3(uint32_t v___x_4201_, lean_object* v_s_4202_){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = lean_string_push(v_s_4202_, v___x_4201_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3___boxed(lean_object* v___x_4204_, lean_object* v_s_4205_){
_start:
{
uint32_t v___x_5743__boxed_4206_; lean_object* v_res_4207_; 
v___x_5743__boxed_4206_ = lean_unbox_uint32(v___x_4204_);
lean_dec(v___x_4204_);
v_res_4207_ = l_Lean_instToMarkdownSnippet___lam__3(v___x_5743__boxed_4206_, v_s_4205_);
return v_res_4207_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = 35;
v___x_4209_ = lean_box_uint32(v___x_4208_);
return v___x_4209_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0(void){
_start:
{
lean_object* v___x_4210_; lean_object* v___f_4211_; 
v___x_4210_ = l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1;
v___f_4211_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__3___boxed), 2, 1);
lean_closure_set(v___f_4211_, 0, v___x_4210_);
return v___f_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4(lean_object* v___x_4212_, lean_object* v___f_4213_, lean_object* v___x_4214_, lean_object* v___f_4215_, lean_object* v_a_4216_, lean_object* v_x_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v_snd_4221_; lean_object* v_fst_4222_; lean_object* v_snd_4223_; lean_object* v___x_4224_; lean_object* v___f_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v_snd_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v_snd_4233_; lean_object* v_title_4234_; lean_object* v_content_4235_; size_t v_sz_4236_; size_t v___x_4237_; lean_object* v___x_5585__overap_4238_; lean_object* v___x_4239_; lean_object* v_snd_4240_; lean_object* v___x_4241_; lean_object* v_snd_4242_; size_t v_sz_4243_; lean_object* v___x_5591__overap_4244_; lean_object* v___x_4245_; lean_object* v_snd_4246_; lean_object* v___x_4247_; lean_object* v_snd_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4256_; 
v_snd_4221_ = lean_ctor_get(v_a_4216_, 1);
lean_inc(v_snd_4221_);
v_fst_4222_ = lean_ctor_get(v_a_4216_, 0);
lean_inc(v_fst_4222_);
lean_dec_ref(v_a_4216_);
v_snd_4223_ = lean_ctor_get(v_snd_4221_, 1);
lean_inc(v_snd_4223_);
lean_dec(v_snd_4221_);
v___x_4224_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___f_4225_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___lam__4___closed__0, &l_Lean_instToMarkdownSnippet___lam__4___closed__0_once, _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0);
v___x_4226_ = lean_unsigned_to_nat(1u);
v___x_4227_ = lean_nat_add(v_fst_4222_, v___x_4226_);
lean_dec(v_fst_4222_);
v___x_4228_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_4225_, v___x_4227_, v___x_4224_);
v___x_4229_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4228_, v___y_4220_);
lean_dec(v___x_4228_);
v_snd_4230_ = lean_ctor_get(v___x_4229_, 1);
lean_inc(v_snd_4230_);
lean_dec_ref(v___x_4229_);
v___x_4231_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0));
v___x_4232_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4231_, v_snd_4230_);
v_snd_4233_ = lean_ctor_get(v___x_4232_, 1);
lean_inc(v_snd_4233_);
lean_dec_ref(v___x_4232_);
v_title_4234_ = lean_ctor_get(v_snd_4223_, 0);
lean_inc_ref(v_title_4234_);
v_content_4235_ = lean_ctor_get(v_snd_4223_, 3);
lean_inc_ref(v_content_4235_);
lean_dec(v_snd_4223_);
v_sz_4236_ = lean_array_size(v_title_4234_);
v___x_4237_ = ((size_t)0ULL);
lean_inc_ref(v___x_4212_);
v___x_5585__overap_4238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4212_, v_title_4234_, v___f_4213_, v_sz_4236_, v___x_4237_, v___x_4214_);
lean_inc_ref(v___y_4219_);
v___x_4239_ = lean_apply_2(v___x_5585__overap_4238_, v___y_4219_, v_snd_4233_);
v_snd_4240_ = lean_ctor_get(v___x_4239_, 1);
lean_inc(v_snd_4240_);
lean_dec_ref(v___x_4239_);
v___x_4241_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4240_);
v_snd_4242_ = lean_ctor_get(v___x_4241_, 1);
lean_inc(v_snd_4242_);
lean_dec_ref(v___x_4241_);
v_sz_4243_ = lean_array_size(v_content_4235_);
v___x_5591__overap_4244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4212_, v_content_4235_, v___f_4215_, v_sz_4243_, v___x_4237_, v___x_4214_);
lean_inc_ref(v___y_4219_);
v___x_4245_ = lean_apply_2(v___x_5591__overap_4244_, v___y_4219_, v_snd_4242_);
v_snd_4246_ = lean_ctor_get(v___x_4245_, 1);
lean_inc(v_snd_4246_);
lean_dec_ref(v___x_4245_);
v___x_4247_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4246_);
v_snd_4248_ = lean_ctor_get(v___x_4247_, 1);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4256_ == 0)
{
lean_object* v_unused_4257_; 
v_unused_4257_ = lean_ctor_get(v___x_4247_, 0);
lean_dec(v_unused_4257_);
v___x_4250_ = v___x_4247_;
v_isShared_4251_ = v_isSharedCheck_4256_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_snd_4248_);
lean_dec(v___x_4247_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4256_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4252_; lean_object* v___x_4254_; 
v___x_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4214_);
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 0, v___x_4252_);
v___x_4254_ = v___x_4250_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4252_);
lean_ctor_set(v_reuseFailAlloc_4255_, 1, v_snd_4248_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4___boxed(lean_object* v___x_4258_, lean_object* v___f_4259_, lean_object* v___x_4260_, lean_object* v___f_4261_, lean_object* v_a_4262_, lean_object* v_x_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Lean_instToMarkdownSnippet___lam__4(v___x_4258_, v___f_4259_, v___x_4260_, v___f_4261_, v_a_4262_, v_x_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec_ref(v___y_4265_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5(lean_object* v___x_4268_, lean_object* v___x_4269_, lean_object* v___x_4270_, lean_object* v___f_4271_, lean_object* v_x_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v_text_4275_; lean_object* v_sections_4276_; lean_object* v_snd_4278_; lean_object* v___y_4299_; lean_object* v___x_4301_; lean_object* v___x_4302_; uint8_t v___x_4303_; 
v_text_4275_ = lean_ctor_get(v_x_4272_, 0);
lean_inc_ref(v_text_4275_);
v_sections_4276_ = lean_ctor_get(v_x_4272_, 1);
lean_inc_ref(v_sections_4276_);
lean_dec_ref(v_x_4272_);
v___x_4301_ = lean_unsigned_to_nat(0u);
v___x_4302_ = lean_array_get_size(v_text_4275_);
v___x_4303_ = lean_nat_dec_lt(v___x_4301_, v___x_4302_);
if (v___x_4303_ == 0)
{
lean_dec_ref(v_text_4275_);
lean_dec_ref(v___f_4271_);
v_snd_4278_ = v___y_4274_;
goto v___jp_4277_;
}
else
{
lean_object* v___x_4304_; uint8_t v___x_4305_; 
v___x_4304_ = lean_box(0);
v___x_4305_ = lean_nat_dec_le(v___x_4302_, v___x_4302_);
if (v___x_4305_ == 0)
{
if (v___x_4303_ == 0)
{
lean_dec_ref(v_text_4275_);
lean_dec_ref(v___f_4271_);
v_snd_4278_ = v___y_4274_;
goto v___jp_4277_;
}
else
{
size_t v___x_4306_; size_t v___x_4307_; lean_object* v___x_5634__overap_4308_; lean_object* v___x_4309_; 
v___x_4306_ = ((size_t)0ULL);
v___x_4307_ = lean_usize_of_nat(v___x_4302_);
lean_inc_ref(v___x_4270_);
v___x_5634__overap_4308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4270_, v___f_4271_, v_text_4275_, v___x_4306_, v___x_4307_, v___x_4304_);
lean_inc_ref(v___y_4273_);
v___x_4309_ = lean_apply_2(v___x_5634__overap_4308_, v___y_4273_, v___y_4274_);
v___y_4299_ = v___x_4309_;
goto v___jp_4298_;
}
}
else
{
size_t v___x_4310_; size_t v___x_4311_; lean_object* v___x_5637__overap_4312_; lean_object* v___x_4313_; 
v___x_4310_ = ((size_t)0ULL);
v___x_4311_ = lean_usize_of_nat(v___x_4302_);
lean_inc_ref(v___x_4270_);
v___x_5637__overap_4312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4270_, v___f_4271_, v_text_4275_, v___x_4310_, v___x_4311_, v___x_4304_);
lean_inc_ref(v___y_4273_);
v___x_4313_ = lean_apply_2(v___x_5637__overap_4312_, v___y_4273_, v___y_4274_);
v___y_4299_ = v___x_4313_;
goto v___jp_4298_;
}
}
v___jp_4277_:
{
lean_object* v___x_4279_; lean_object* v_snd_4280_; lean_object* v___x_4281_; lean_object* v___f_4282_; lean_object* v___f_4283_; lean_object* v___f_4284_; size_t v_sz_4285_; size_t v___x_4286_; lean_object* v___x_5619__overap_4287_; lean_object* v___x_4288_; lean_object* v_snd_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
v___x_4279_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4278_);
v_snd_4280_ = lean_ctor_get(v___x_4279_, 1);
lean_inc(v_snd_4280_);
lean_dec_ref(v___x_4279_);
v___x_4281_ = lean_box(0);
lean_inc_ref(v___x_4268_);
v___f_4282_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__1___boxed), 8, 3);
lean_closure_set(v___f_4282_, 0, v___x_4268_);
lean_closure_set(v___f_4282_, 1, v___x_4269_);
lean_closure_set(v___f_4282_, 2, v___x_4281_);
v___f_4283_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_4283_, 0, v___x_4268_);
lean_closure_set(v___f_4283_, 1, v___x_4281_);
lean_inc_ref(v___x_4270_);
v___f_4284_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__4___boxed), 9, 4);
lean_closure_set(v___f_4284_, 0, v___x_4270_);
lean_closure_set(v___f_4284_, 1, v___f_4283_);
lean_closure_set(v___f_4284_, 2, v___x_4281_);
lean_closure_set(v___f_4284_, 3, v___f_4282_);
v_sz_4285_ = lean_array_size(v_sections_4276_);
v___x_4286_ = ((size_t)0ULL);
v___x_5619__overap_4287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4270_, v_sections_4276_, v___f_4284_, v_sz_4285_, v___x_4286_, v___x_4281_);
lean_inc_ref(v___y_4273_);
v___x_4288_ = lean_apply_2(v___x_5619__overap_4287_, v___y_4273_, v_snd_4280_);
v_snd_4289_ = lean_ctor_get(v___x_4288_, 1);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4296_ == 0)
{
lean_object* v_unused_4297_; 
v_unused_4297_ = lean_ctor_get(v___x_4288_, 0);
lean_dec(v_unused_4297_);
v___x_4291_ = v___x_4288_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_snd_4289_);
lean_dec(v___x_4288_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
lean_ctor_set(v___x_4291_, 0, v___x_4281_);
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4281_);
lean_ctor_set(v_reuseFailAlloc_4295_, 1, v_snd_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
v___jp_4298_:
{
lean_object* v_snd_4300_; 
v_snd_4300_ = lean_ctor_get(v___y_4299_, 1);
lean_inc(v_snd_4300_);
lean_dec_ref(v___y_4299_);
v_snd_4278_ = v_snd_4300_;
goto v___jp_4277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5___boxed(lean_object* v___x_4314_, lean_object* v___x_4315_, lean_object* v___x_4316_, lean_object* v___f_4317_, lean_object* v_x_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_Lean_instToMarkdownSnippet___lam__5(v___x_4314_, v___x_4315_, v___x_4316_, v___f_4317_, v_x_4318_, v___y_4319_, v___y_4320_);
lean_dec_ref(v___y_4319_);
return v_res_4321_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___f_4324_; 
v___x_4322_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4323_ = l_Lean_instMarkdownInlineElabInline;
v___f_4324_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__0___boxed), 6, 2);
lean_closure_set(v___f_4324_, 0, v___x_4323_);
lean_closure_set(v___f_4324_, 1, v___x_4322_);
return v___f_4324_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__1(void){
_start:
{
lean_object* v___f_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___f_4329_; 
v___f_4325_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__0, &l_Lean_instToMarkdownSnippet___closed__0_once, _init_l_Lean_instToMarkdownSnippet___closed__0);
v___x_4326_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___x_4327_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4328_ = l_Lean_instMarkdownInlineElabInline;
v___f_4329_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__5___boxed), 7, 4);
lean_closure_set(v___f_4329_, 0, v___x_4328_);
lean_closure_set(v___f_4329_, 1, v___x_4327_);
lean_closure_set(v___f_4329_, 2, v___x_4326_);
lean_closure_set(v___f_4329_, 3, v___f_4325_);
return v___f_4329_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet(void){
_start:
{
lean_object* v___f_4330_; 
v___f_4330_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__1, &l_Lean_instToMarkdownSnippet___closed__1_once, _init_l_Lean_instToMarkdownSnippet___closed__1);
return v___f_4330_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0(void){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_4331_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4332_ = lean_box(0);
v___x_4333_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
lean_ctor_set(v___x_4334_, 1, v___x_4332_);
return v___x_4334_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default(void){
_start:
{
lean_object* v___x_4335_; 
v___x_4335_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
return v___x_4335_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs(void){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_Lean_instInhabitedVersoModuleDocs_default;
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object* v___x_4343_, lean_object* v_v_4344_, lean_object* v_x_4345_){
_start:
{
lean_object* v_snippets_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4369_; 
v_snippets_4346_ = lean_ctor_get(v_v_4344_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v_v_4344_);
if (v_isSharedCheck_4369_ == 0)
{
lean_object* v_unused_4370_; 
v_unused_4370_ = lean_ctor_get(v_v_4344_, 1);
lean_dec(v_unused_4370_);
v___x_4348_ = v_v_4344_;
v_isShared_4349_ = v_isSharedCheck_4369_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_snippets_4346_);
lean_dec(v_v_4344_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4369_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4350_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___x_4351_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_4352_ = lean_box(1);
v___x_4353_ = ((lean_object*)(l_Lean_instReprVersoModuleDocs___lam__0___closed__2));
v___x_4354_ = l_Lean_PersistentArray_toArray___redArg(v_snippets_4346_);
lean_dec_ref(v_snippets_4346_);
v___x_4355_ = l_Array_repr___redArg(v___x_4343_, v___x_4354_);
if (v_isShared_4349_ == 0)
{
lean_ctor_set_tag(v___x_4348_, 5);
lean_ctor_set(v___x_4348_, 1, v___x_4355_);
lean_ctor_set(v___x_4348_, 0, v___x_4353_);
v___x_4357_ = v___x_4348_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v___x_4353_);
lean_ctor_set(v_reuseFailAlloc_4368_, 1, v___x_4355_);
v___x_4357_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4358_; uint8_t v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4358_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4350_);
lean_ctor_set(v___x_4358_, 1, v___x_4357_);
v___x_4359_ = 0;
v___x_4360_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4360_, 0, v___x_4358_);
lean_ctor_set_uint8(v___x_4360_, sizeof(void*)*1, v___x_4359_);
lean_inc_ref(v___x_4360_);
v___x_4361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4351_);
lean_ctor_set(v___x_4361_, 1, v___x_4360_);
v___x_4362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
lean_ctor_set(v___x_4362_, 1, v___x_4352_);
v___x_4363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
lean_ctor_set(v___x_4363_, 1, v___x_4360_);
v___x_4364_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_4365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4363_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4350_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
lean_ctor_set_uint8(v___x_4367_, sizeof(void*)*1, v___x_4359_);
return v___x_4367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object* v___x_4371_, lean_object* v_v_4372_, lean_object* v_x_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Lean_instReprVersoModuleDocs___lam__0(v___x_4371_, v_v_4372_, v_x_4373_);
lean_dec(v_x_4373_);
return v_res_4374_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object* v_docs_4378_){
_start:
{
lean_object* v_snippets_4379_; uint8_t v___x_4380_; 
v_snippets_4379_ = lean_ctor_get(v_docs_4378_, 0);
v___x_4380_ = l_Lean_PersistentArray_isEmpty___redArg(v_snippets_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object* v_docs_4381_){
_start:
{
uint8_t v_res_4382_; lean_object* v_r_4383_; 
v_res_4382_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_4381_);
lean_dec_ref(v_docs_4381_);
v_r_4383_ = lean_box(v_res_4382_);
return v_r_4383_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object* v_docs_4384_, lean_object* v_snippet_4385_){
_start:
{
lean_object* v_terminalNesting_4386_; 
v_terminalNesting_4386_ = lean_ctor_get(v_docs_4384_, 1);
if (lean_obj_tag(v_terminalNesting_4386_) == 1)
{
lean_object* v_val_4387_; uint8_t v___x_4388_; 
v_val_4387_ = lean_ctor_get(v_terminalNesting_4386_, 0);
v___x_4388_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4387_, v_snippet_4385_);
return v___x_4388_;
}
else
{
uint8_t v___x_4389_; 
v___x_4389_ = 1;
return v___x_4389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object* v_docs_4390_, lean_object* v_snippet_4391_){
_start:
{
uint8_t v_res_4392_; lean_object* v_r_4393_; 
v_res_4392_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4390_, v_snippet_4391_);
lean_dec_ref(v_snippet_4391_);
lean_dec_ref(v_docs_4390_);
v_r_4393_ = lean_box(v_res_4392_);
return v_r_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object* v_docs_4397_, lean_object* v_snippet_4398_){
_start:
{
uint8_t v___x_4399_; 
v___x_4399_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4397_, v_snippet_4398_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; 
lean_dec_ref(v_snippet_4398_);
lean_dec_ref(v_docs_4397_);
v___x_4400_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__1));
return v___x_4400_;
}
else
{
lean_object* v_snippets_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4411_; 
v_snippets_4401_ = lean_ctor_get(v_docs_4397_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v_docs_4397_);
if (v_isSharedCheck_4411_ == 0)
{
lean_object* v_unused_4412_; 
v_unused_4412_ = lean_ctor_get(v_docs_4397_, 1);
lean_dec(v_unused_4412_);
v___x_4403_ = v_docs_4397_;
v_isShared_4404_ = v_isSharedCheck_4411_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_snippets_4401_);
lean_dec(v_docs_4397_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4411_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4408_; 
lean_inc_ref(v_snippet_4398_);
v___x_4405_ = l_Lean_PersistentArray_push___redArg(v_snippets_4401_, v_snippet_4398_);
v___x_4406_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4398_);
lean_dec_ref(v_snippet_4398_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 1, v___x_4406_);
lean_ctor_set(v___x_4403_, 0, v___x_4405_);
v___x_4408_ = v___x_4403_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4405_);
lean_ctor_set(v_reuseFailAlloc_4410_, 1, v___x_4406_);
v___x_4408_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
lean_object* v___x_4409_; 
v___x_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
return v___x_4409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object* v_msg_4413_){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4414_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_4415_ = lean_panic_fn_borrowed(v___x_4414_, v_msg_4413_);
return v___x_4415_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_add_x21___closed__2(void){
_start:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4418_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__0));
v___x_4419_ = lean_unsigned_to_nat(4u);
v___x_4420_ = lean_unsigned_to_nat(336u);
v___x_4421_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__1));
v___x_4422_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__0));
v___x_4423_ = l_mkPanicMessageWithDecl(v___x_4422_, v___x_4421_, v___x_4420_, v___x_4419_, v___x_4418_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object* v_docs_4424_, lean_object* v_snippet_4425_){
_start:
{
lean_object* v_snippets_4426_; lean_object* v_terminalNesting_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4441_; 
v_snippets_4426_ = lean_ctor_get(v_docs_4424_, 0);
v_terminalNesting_4427_ = lean_ctor_get(v_docs_4424_, 1);
v_isSharedCheck_4441_ = !lean_is_exclusive(v_docs_4424_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4429_ = v_docs_4424_;
v_isShared_4430_ = v_isSharedCheck_4441_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_terminalNesting_4427_);
lean_inc(v_snippets_4426_);
lean_dec(v_docs_4424_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4441_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
if (lean_obj_tag(v_terminalNesting_4427_) == 1)
{
lean_object* v_val_4437_; uint8_t v___x_4438_; 
v_val_4437_ = lean_ctor_get(v_terminalNesting_4427_, 0);
lean_inc(v_val_4437_);
lean_dec_ref(v_terminalNesting_4427_);
v___x_4438_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4437_, v_snippet_4425_);
lean_dec(v_val_4437_);
if (v___x_4438_ == 0)
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
lean_del_object(v___x_4429_);
lean_dec_ref(v_snippets_4426_);
lean_dec_ref(v_snippet_4425_);
v___x_4439_ = lean_obj_once(&l_Lean_VersoModuleDocs_add_x21___closed__2, &l_Lean_VersoModuleDocs_add_x21___closed__2_once, _init_l_Lean_VersoModuleDocs_add_x21___closed__2);
v___x_4440_ = l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(v___x_4439_);
return v___x_4440_;
}
else
{
goto v___jp_4431_;
}
}
else
{
lean_dec(v_terminalNesting_4427_);
goto v___jp_4431_;
}
v___jp_4431_:
{
lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4435_; 
lean_inc_ref(v_snippet_4425_);
v___x_4432_ = l_Lean_PersistentArray_push___redArg(v_snippets_4426_, v_snippet_4425_);
v___x_4433_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4425_);
lean_dec_ref(v_snippet_4425_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 1, v___x_4433_);
lean_ctor_set(v___x_4429_, 0, v___x_4432_);
v___x_4435_ = v___x_4429_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4432_);
lean_ctor_set(v_reuseFailAlloc_4436_, 1, v___x_4433_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object* v_ctx_4442_){
_start:
{
lean_object* v_context_4443_; lean_object* v___x_4444_; 
v_context_4443_ = lean_ctor_get(v_ctx_4442_, 2);
v___x_4444_ = lean_array_get_size(v_context_4443_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object* v_ctx_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4445_);
lean_dec_ref(v_ctx_4445_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object* v_ctx_4450_){
_start:
{
lean_object* v_content_4451_; lean_object* v_priorParts_4452_; lean_object* v_context_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4476_; 
v_content_4451_ = lean_ctor_get(v_ctx_4450_, 0);
v_priorParts_4452_ = lean_ctor_get(v_ctx_4450_, 1);
v_context_4453_ = lean_ctor_get(v_ctx_4450_, 2);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_ctx_4450_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4455_ = v_ctx_4450_;
v_isShared_4456_ = v_isSharedCheck_4476_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_context_4453_);
lean_inc(v_priorParts_4452_);
lean_inc(v_content_4451_);
lean_dec(v_ctx_4450_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4476_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; uint8_t v___x_4459_; 
v___x_4457_ = lean_array_get_size(v_context_4453_);
v___x_4458_ = lean_unsigned_to_nat(0u);
v___x_4459_ = lean_nat_dec_eq(v___x_4457_, v___x_4458_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v_last_4462_; lean_object* v_content_4463_; lean_object* v_priorParts_4464_; lean_object* v_titleString_4465_; lean_object* v_title_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4472_; 
v___x_4460_ = lean_unsigned_to_nat(1u);
v___x_4461_ = lean_nat_sub(v___x_4457_, v___x_4460_);
v_last_4462_ = lean_array_fget_borrowed(v_context_4453_, v___x_4461_);
lean_dec(v___x_4461_);
v_content_4463_ = lean_ctor_get(v_last_4462_, 0);
lean_inc_ref(v_content_4463_);
v_priorParts_4464_ = lean_ctor_get(v_last_4462_, 1);
v_titleString_4465_ = lean_ctor_get(v_last_4462_, 2);
v_title_4466_ = lean_ctor_get(v_last_4462_, 3);
v___x_4467_ = lean_box(0);
lean_inc_ref(v_titleString_4465_);
lean_inc_ref(v_title_4466_);
v___x_4468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4468_, 0, v_title_4466_);
lean_ctor_set(v___x_4468_, 1, v_titleString_4465_);
lean_ctor_set(v___x_4468_, 2, v___x_4467_);
lean_ctor_set(v___x_4468_, 3, v_content_4451_);
lean_ctor_set(v___x_4468_, 4, v_priorParts_4452_);
lean_inc_ref(v_priorParts_4464_);
v___x_4469_ = lean_array_push(v_priorParts_4464_, v___x_4468_);
v___x_4470_ = lean_array_pop(v_context_4453_);
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 2, v___x_4470_);
lean_ctor_set(v___x_4455_, 1, v___x_4469_);
lean_ctor_set(v___x_4455_, 0, v_content_4463_);
v___x_4472_ = v___x_4455_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_content_4463_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v___x_4469_);
lean_ctor_set(v_reuseFailAlloc_4474_, 2, v___x_4470_);
v___x_4472_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
lean_object* v___x_4473_; 
v___x_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4472_);
return v___x_4473_;
}
}
else
{
lean_object* v___x_4475_; 
lean_del_object(v___x_4455_);
lean_dec_ref(v_context_4453_);
lean_dec_ref(v_priorParts_4452_);
lean_dec_ref(v_content_4451_);
v___x_4475_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1));
return v___x_4475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object* v_ctx_4477_){
_start:
{
lean_object* v_context_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; uint8_t v___x_4481_; 
v_context_4478_ = lean_ctor_get(v_ctx_4477_, 2);
v___x_4479_ = lean_array_get_size(v_context_4478_);
v___x_4480_ = lean_unsigned_to_nat(0u);
v___x_4481_ = lean_nat_dec_eq(v___x_4479_, v___x_4480_);
if (v___x_4481_ == 0)
{
lean_object* v___x_4482_; 
v___x_4482_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4477_);
if (lean_obj_tag(v___x_4482_) == 0)
{
return v___x_4482_;
}
else
{
lean_object* v_a_4483_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_a_4483_);
lean_dec_ref(v___x_4482_);
v_ctx_4477_ = v_a_4483_;
goto _start;
}
}
else
{
lean_object* v___x_4485_; 
v___x_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4485_, 0, v_ctx_4477_);
return v___x_4485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object* v_ctx_4488_, lean_object* v_partLevel_4489_, lean_object* v_part_4490_){
_start:
{
lean_object* v___x_4491_; uint8_t v___x_4492_; 
v___x_4491_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4488_);
v___x_4492_ = lean_nat_dec_lt(v___x_4491_, v_partLevel_4489_);
if (v___x_4492_ == 0)
{
uint8_t v___x_4493_; 
v___x_4493_ = lean_nat_dec_eq(v_partLevel_4489_, v___x_4491_);
lean_dec(v___x_4491_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4494_; 
v___x_4494_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4488_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_dec_ref(v_part_4490_);
lean_dec(v_partLevel_4489_);
return v___x_4494_;
}
else
{
lean_object* v_a_4495_; 
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_a_4495_);
lean_dec_ref(v___x_4494_);
v_ctx_4488_ = v_a_4495_;
goto _start;
}
}
else
{
lean_object* v_content_4497_; lean_object* v_priorParts_4498_; lean_object* v_context_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4508_; 
lean_dec(v_partLevel_4489_);
v_content_4497_ = lean_ctor_get(v_ctx_4488_, 0);
v_priorParts_4498_ = lean_ctor_get(v_ctx_4488_, 1);
v_context_4499_ = lean_ctor_get(v_ctx_4488_, 2);
v_isSharedCheck_4508_ = !lean_is_exclusive(v_ctx_4488_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4501_ = v_ctx_4488_;
v_isShared_4502_ = v_isSharedCheck_4508_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_context_4499_);
lean_inc(v_priorParts_4498_);
lean_inc(v_content_4497_);
lean_dec(v_ctx_4488_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4508_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4503_; lean_object* v___x_4505_; 
v___x_4503_ = lean_array_push(v_priorParts_4498_, v_part_4490_);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 1, v___x_4503_);
v___x_4505_ = v___x_4501_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_content_4497_);
lean_ctor_set(v_reuseFailAlloc_4507_, 1, v___x_4503_);
lean_ctor_set(v_reuseFailAlloc_4507_, 2, v_context_4499_);
v___x_4505_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4506_; 
v___x_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
return v___x_4506_;
}
}
}
}
else
{
lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
lean_dec_ref(v_part_4490_);
lean_dec_ref(v_ctx_4488_);
v___x_4509_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0));
v___x_4510_ = l_Nat_reprFast(v___x_4491_);
v___x_4511_ = lean_string_append(v___x_4509_, v___x_4510_);
lean_dec_ref(v___x_4510_);
v___x_4512_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1));
v___x_4513_ = lean_string_append(v___x_4511_, v___x_4512_);
v___x_4514_ = l_Nat_reprFast(v_partLevel_4489_);
v___x_4515_ = lean_string_append(v___x_4513_, v___x_4514_);
lean_dec_ref(v___x_4514_);
v___x_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
return v___x_4516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object* v_ctx_4520_, lean_object* v_blocks_4521_){
_start:
{
lean_object* v_content_4522_; lean_object* v_priorParts_4523_; lean_object* v_context_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4537_; 
v_content_4522_ = lean_ctor_get(v_ctx_4520_, 0);
v_priorParts_4523_ = lean_ctor_get(v_ctx_4520_, 1);
v_context_4524_ = lean_ctor_get(v_ctx_4520_, 2);
v_isSharedCheck_4537_ = !lean_is_exclusive(v_ctx_4520_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4526_ = v_ctx_4520_;
v_isShared_4527_ = v_isSharedCheck_4537_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_context_4524_);
lean_inc(v_priorParts_4523_);
lean_inc(v_content_4522_);
lean_dec(v_ctx_4520_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4537_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4528_ = lean_array_get_size(v_priorParts_4523_);
v___x_4529_ = lean_unsigned_to_nat(0u);
v___x_4530_ = lean_nat_dec_eq(v___x_4528_, v___x_4529_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; 
lean_del_object(v___x_4526_);
lean_dec_ref(v_context_4524_);
lean_dec_ref(v_priorParts_4523_);
lean_dec_ref(v_content_4522_);
v___x_4531_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1));
return v___x_4531_;
}
else
{
lean_object* v___x_4532_; lean_object* v___x_4534_; 
v___x_4532_ = l_Array_append___redArg(v_content_4522_, v_blocks_4521_);
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 0, v___x_4532_);
v___x_4534_ = v___x_4526_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4532_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v_priorParts_4523_);
lean_ctor_set(v_reuseFailAlloc_4536_, 2, v_context_4524_);
v___x_4534_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
lean_object* v___x_4535_; 
v___x_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4534_);
return v___x_4535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object* v_ctx_4538_, lean_object* v_blocks_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4538_, v_blocks_4539_);
lean_dec_ref(v_blocks_4539_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object* v_as_4541_, size_t v_sz_4542_, size_t v_i_4543_, lean_object* v_b_4544_){
_start:
{
uint8_t v___x_4545_; 
v___x_4545_ = lean_usize_dec_lt(v_i_4543_, v_sz_4542_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; 
v___x_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4546_, 0, v_b_4544_);
return v___x_4546_;
}
else
{
lean_object* v_a_4547_; lean_object* v_snd_4548_; lean_object* v_fst_4549_; lean_object* v_snd_4550_; lean_object* v___x_4551_; 
v_a_4547_ = lean_array_uget_borrowed(v_as_4541_, v_i_4543_);
v_snd_4548_ = lean_ctor_get(v_a_4547_, 1);
v_fst_4549_ = lean_ctor_get(v_a_4547_, 0);
v_snd_4550_ = lean_ctor_get(v_snd_4548_, 1);
lean_inc(v_snd_4550_);
lean_inc(v_fst_4549_);
v___x_4551_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(v_b_4544_, v_fst_4549_, v_snd_4550_);
if (lean_obj_tag(v___x_4551_) == 0)
{
return v___x_4551_;
}
else
{
lean_object* v_a_4552_; size_t v___x_4553_; size_t v___x_4554_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref(v___x_4551_);
v___x_4553_ = ((size_t)1ULL);
v___x_4554_ = lean_usize_add(v_i_4543_, v___x_4553_);
v_i_4543_ = v___x_4554_;
v_b_4544_ = v_a_4552_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object* v_as_4556_, lean_object* v_sz_4557_, lean_object* v_i_4558_, lean_object* v_b_4559_){
_start:
{
size_t v_sz_boxed_4560_; size_t v_i_boxed_4561_; lean_object* v_res_4562_; 
v_sz_boxed_4560_ = lean_unbox_usize(v_sz_4557_);
lean_dec(v_sz_4557_);
v_i_boxed_4561_ = lean_unbox_usize(v_i_4558_);
lean_dec(v_i_4558_);
v_res_4562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_4556_, v_sz_boxed_4560_, v_i_boxed_4561_, v_b_4559_);
lean_dec_ref(v_as_4556_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object* v_ctx_4563_, lean_object* v_snippet_4564_){
_start:
{
lean_object* v_text_4565_; lean_object* v_sections_4566_; lean_object* v___x_4567_; 
v_text_4565_ = lean_ctor_get(v_snippet_4564_, 0);
v_sections_4566_ = lean_ctor_get(v_snippet_4564_, 1);
v___x_4567_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4563_, v_text_4565_);
if (lean_obj_tag(v___x_4567_) == 0)
{
return v___x_4567_;
}
else
{
lean_object* v_a_4568_; size_t v_sz_4569_; size_t v___x_4570_; lean_object* v___x_4571_; 
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc(v_a_4568_);
lean_dec_ref(v___x_4567_);
v_sz_4569_ = lean_array_size(v_sections_4566_);
v___x_4570_ = ((size_t)0ULL);
v___x_4571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_sections_4566_, v_sz_4569_, v___x_4570_, v_a_4568_);
return v___x_4571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object* v_ctx_4572_, lean_object* v_snippet_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_ctx_4572_, v_snippet_4573_);
lean_dec_ref(v_snippet_4573_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object* v_as_4575_, size_t v_sz_4576_, size_t v_i_4577_, lean_object* v_b_4578_){
_start:
{
uint8_t v___x_4579_; 
v___x_4579_ = lean_usize_dec_lt(v_i_4577_, v_sz_4576_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; 
v___x_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4580_, 0, v_b_4578_);
return v___x_4580_;
}
else
{
lean_object* v_snd_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4603_; 
v_snd_4581_ = lean_ctor_get(v_b_4578_, 1);
v_isSharedCheck_4603_ = !lean_is_exclusive(v_b_4578_);
if (v_isSharedCheck_4603_ == 0)
{
lean_object* v_unused_4604_; 
v_unused_4604_ = lean_ctor_get(v_b_4578_, 0);
lean_dec(v_unused_4604_);
v___x_4583_ = v_b_4578_;
v_isShared_4584_ = v_isSharedCheck_4603_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_snd_4581_);
lean_dec(v_b_4578_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4603_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v_a_4585_; lean_object* v___x_4586_; 
v_a_4585_ = lean_array_uget_borrowed(v_as_4575_, v_i_4577_);
v___x_4586_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4581_, v_a_4585_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
lean_del_object(v___x_4583_);
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4586_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4586_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4596_; lean_object* v___x_4598_; 
v_a_4595_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4595_);
lean_dec_ref(v___x_4586_);
v___x_4596_ = lean_box(0);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 1, v_a_4595_);
lean_ctor_set(v___x_4583_, 0, v___x_4596_);
v___x_4598_ = v___x_4583_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4596_);
lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_a_4595_);
v___x_4598_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
size_t v___x_4599_; size_t v___x_4600_; 
v___x_4599_ = ((size_t)1ULL);
v___x_4600_ = lean_usize_add(v_i_4577_, v___x_4599_);
v_i_4577_ = v___x_4600_;
v_b_4578_ = v___x_4598_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4605_, lean_object* v_sz_4606_, lean_object* v_i_4607_, lean_object* v_b_4608_){
_start:
{
size_t v_sz_boxed_4609_; size_t v_i_boxed_4610_; lean_object* v_res_4611_; 
v_sz_boxed_4609_ = lean_unbox_usize(v_sz_4606_);
lean_dec(v_sz_4606_);
v_i_boxed_4610_ = lean_unbox_usize(v_i_4607_);
lean_dec(v_i_4607_);
v_res_4611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4605_, v_sz_boxed_4609_, v_i_boxed_4610_, v_b_4608_);
lean_dec_ref(v_as_4605_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object* v_as_4612_, size_t v_sz_4613_, size_t v_i_4614_, lean_object* v_b_4615_){
_start:
{
uint8_t v___x_4616_; 
v___x_4616_ = lean_usize_dec_lt(v_i_4614_, v_sz_4613_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; 
v___x_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4617_, 0, v_b_4615_);
return v___x_4617_;
}
else
{
lean_object* v_snd_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4640_; 
v_snd_4618_ = lean_ctor_get(v_b_4615_, 1);
v_isSharedCheck_4640_ = !lean_is_exclusive(v_b_4615_);
if (v_isSharedCheck_4640_ == 0)
{
lean_object* v_unused_4641_; 
v_unused_4641_ = lean_ctor_get(v_b_4615_, 0);
lean_dec(v_unused_4641_);
v___x_4620_ = v_b_4615_;
v_isShared_4621_ = v_isSharedCheck_4640_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_snd_4618_);
lean_dec(v_b_4615_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4640_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v_a_4622_; lean_object* v___x_4623_; 
v_a_4622_ = lean_array_uget_borrowed(v_as_4612_, v_i_4614_);
v___x_4623_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4618_, v_a_4622_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_del_object(v___x_4620_);
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4623_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4633_; lean_object* v___x_4635_; 
v_a_4632_ = lean_ctor_get(v___x_4623_, 0);
lean_inc(v_a_4632_);
lean_dec_ref(v___x_4623_);
v___x_4633_ = lean_box(0);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 1, v_a_4632_);
lean_ctor_set(v___x_4620_, 0, v___x_4633_);
v___x_4635_ = v___x_4620_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4633_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_a_4632_);
v___x_4635_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
size_t v___x_4636_; size_t v___x_4637_; lean_object* v___x_4638_; 
v___x_4636_ = ((size_t)1ULL);
v___x_4637_ = lean_usize_add(v_i_4614_, v___x_4636_);
v___x_4638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4612_, v_sz_4613_, v___x_4637_, v___x_4635_);
return v___x_4638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object* v_as_4642_, lean_object* v_sz_4643_, lean_object* v_i_4644_, lean_object* v_b_4645_){
_start:
{
size_t v_sz_boxed_4646_; size_t v_i_boxed_4647_; lean_object* v_res_4648_; 
v_sz_boxed_4646_ = lean_unbox_usize(v_sz_4643_);
lean_dec(v_sz_4643_);
v_i_boxed_4647_ = lean_unbox_usize(v_i_4644_);
lean_dec(v_i_4644_);
v_res_4648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_4642_, v_sz_boxed_4646_, v_i_boxed_4647_, v_b_4645_);
lean_dec_ref(v_as_4642_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_4649_, size_t v_sz_4650_, size_t v_i_4651_, lean_object* v_b_4652_){
_start:
{
uint8_t v___x_4653_; 
v___x_4653_ = lean_usize_dec_lt(v_i_4651_, v_sz_4650_);
if (v___x_4653_ == 0)
{
lean_object* v___x_4654_; 
v___x_4654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4654_, 0, v_b_4652_);
return v___x_4654_;
}
else
{
lean_object* v_snd_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4677_; 
v_snd_4655_ = lean_ctor_get(v_b_4652_, 1);
v_isSharedCheck_4677_ = !lean_is_exclusive(v_b_4652_);
if (v_isSharedCheck_4677_ == 0)
{
lean_object* v_unused_4678_; 
v_unused_4678_ = lean_ctor_get(v_b_4652_, 0);
lean_dec(v_unused_4678_);
v___x_4657_ = v_b_4652_;
v_isShared_4658_ = v_isSharedCheck_4677_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_snd_4655_);
lean_dec(v_b_4652_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4677_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v_a_4659_; lean_object* v___x_4660_; 
v_a_4659_ = lean_array_uget_borrowed(v_as_4649_, v_i_4651_);
v___x_4660_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4655_, v_a_4659_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4668_; 
lean_del_object(v___x_4657_);
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4663_ = v___x_4660_;
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_a_4661_);
lean_dec(v___x_4660_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4666_; 
if (v_isShared_4664_ == 0)
{
v___x_4666_ = v___x_4663_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v_a_4661_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4670_; lean_object* v___x_4672_; 
v_a_4669_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4669_);
lean_dec_ref(v___x_4660_);
v___x_4670_ = lean_box(0);
if (v_isShared_4658_ == 0)
{
lean_ctor_set(v___x_4657_, 1, v_a_4669_);
lean_ctor_set(v___x_4657_, 0, v___x_4670_);
v___x_4672_ = v___x_4657_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_a_4669_);
v___x_4672_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
size_t v___x_4673_; size_t v___x_4674_; 
v___x_4673_ = ((size_t)1ULL);
v___x_4674_ = lean_usize_add(v_i_4651_, v___x_4673_);
v_i_4651_ = v___x_4674_;
v_b_4652_ = v___x_4672_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_4679_, lean_object* v_sz_4680_, lean_object* v_i_4681_, lean_object* v_b_4682_){
_start:
{
size_t v_sz_boxed_4683_; size_t v_i_boxed_4684_; lean_object* v_res_4685_; 
v_sz_boxed_4683_ = lean_unbox_usize(v_sz_4680_);
lean_dec(v_sz_4680_);
v_i_boxed_4684_ = lean_unbox_usize(v_i_4681_);
lean_dec(v_i_4681_);
v_res_4685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4679_, v_sz_boxed_4683_, v_i_boxed_4684_, v_b_4682_);
lean_dec_ref(v_as_4679_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object* v_as_4686_, size_t v_sz_4687_, size_t v_i_4688_, lean_object* v_b_4689_){
_start:
{
uint8_t v___x_4690_; 
v___x_4690_ = lean_usize_dec_lt(v_i_4688_, v_sz_4687_);
if (v___x_4690_ == 0)
{
lean_object* v___x_4691_; 
v___x_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4691_, 0, v_b_4689_);
return v___x_4691_;
}
else
{
lean_object* v_snd_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4714_; 
v_snd_4692_ = lean_ctor_get(v_b_4689_, 1);
v_isSharedCheck_4714_ = !lean_is_exclusive(v_b_4689_);
if (v_isSharedCheck_4714_ == 0)
{
lean_object* v_unused_4715_; 
v_unused_4715_ = lean_ctor_get(v_b_4689_, 0);
lean_dec(v_unused_4715_);
v___x_4694_ = v_b_4689_;
v_isShared_4695_ = v_isSharedCheck_4714_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_snd_4692_);
lean_dec(v_b_4689_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4714_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v_a_4696_; lean_object* v___x_4697_; 
v_a_4696_ = lean_array_uget_borrowed(v_as_4686_, v_i_4688_);
v___x_4697_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4692_, v_a_4696_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4705_; 
lean_del_object(v___x_4694_);
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4700_ = v___x_4697_;
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4697_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
else
{
lean_object* v_a_4706_; lean_object* v___x_4707_; lean_object* v___x_4709_; 
v_a_4706_ = lean_ctor_get(v___x_4697_, 0);
lean_inc(v_a_4706_);
lean_dec_ref(v___x_4697_);
v___x_4707_ = lean_box(0);
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 1, v_a_4706_);
lean_ctor_set(v___x_4694_, 0, v___x_4707_);
v___x_4709_ = v___x_4694_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4707_);
lean_ctor_set(v_reuseFailAlloc_4713_, 1, v_a_4706_);
v___x_4709_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
size_t v___x_4710_; size_t v___x_4711_; lean_object* v___x_4712_; 
v___x_4710_ = ((size_t)1ULL);
v___x_4711_ = lean_usize_add(v_i_4688_, v___x_4710_);
v___x_4712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4686_, v_sz_4687_, v___x_4711_, v___x_4709_);
return v___x_4712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4716_, lean_object* v_sz_4717_, lean_object* v_i_4718_, lean_object* v_b_4719_){
_start:
{
size_t v_sz_boxed_4720_; size_t v_i_boxed_4721_; lean_object* v_res_4722_; 
v_sz_boxed_4720_ = lean_unbox_usize(v_sz_4717_);
lean_dec(v_sz_4717_);
v_i_boxed_4721_ = lean_unbox_usize(v_i_4718_);
lean_dec(v_i_4718_);
v_res_4722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_4716_, v_sz_boxed_4720_, v_i_boxed_4721_, v_b_4719_);
lean_dec_ref(v_as_4716_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object* v_inh_4723_, lean_object* v_n_4724_, lean_object* v_b_4725_){
_start:
{
if (lean_obj_tag(v_n_4724_) == 0)
{
lean_object* v_cs_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4760_; 
v_cs_4726_ = lean_ctor_get(v_n_4724_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v_n_4724_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4728_ = v_n_4724_;
v_isShared_4729_ = v_isSharedCheck_4760_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_cs_4726_);
lean_dec(v_n_4724_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4760_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; size_t v_sz_4732_; size_t v___x_4733_; lean_object* v___x_4734_; 
v___x_4730_ = lean_box(0);
v___x_4731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4730_);
lean_ctor_set(v___x_4731_, 1, v_b_4725_);
v_sz_4732_ = lean_array_size(v_cs_4726_);
v___x_4733_ = ((size_t)0ULL);
v___x_4734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_inh_4723_, v_cs_4726_, v_sz_4732_, v___x_4733_, v___x_4731_);
lean_dec_ref(v_cs_4726_);
if (lean_obj_tag(v___x_4734_) == 0)
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
lean_del_object(v___x_4728_);
v_a_4735_ = lean_ctor_get(v___x_4734_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___x_4734_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4734_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4759_; 
v_a_4743_ = lean_ctor_get(v___x_4734_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4745_ = v___x_4734_;
v_isShared_4746_ = v_isSharedCheck_4759_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4734_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4759_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v_fst_4747_; 
v_fst_4747_ = lean_ctor_get(v_a_4743_, 0);
if (lean_obj_tag(v_fst_4747_) == 0)
{
lean_object* v_snd_4748_; lean_object* v___x_4750_; 
v_snd_4748_ = lean_ctor_get(v_a_4743_, 1);
lean_inc(v_snd_4748_);
lean_dec(v_a_4743_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set_tag(v___x_4728_, 1);
lean_ctor_set(v___x_4728_, 0, v_snd_4748_);
v___x_4750_ = v___x_4728_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_snd_4748_);
v___x_4750_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
lean_object* v___x_4752_; 
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 0, v___x_4750_);
v___x_4752_ = v___x_4745_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4750_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
else
{
lean_object* v_val_4755_; lean_object* v___x_4757_; 
lean_inc_ref(v_fst_4747_);
lean_dec(v_a_4743_);
lean_del_object(v___x_4728_);
v_val_4755_ = lean_ctor_get(v_fst_4747_, 0);
lean_inc(v_val_4755_);
lean_dec_ref(v_fst_4747_);
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 0, v_val_4755_);
v___x_4757_ = v___x_4745_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_val_4755_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
}
}
else
{
lean_object* v_vs_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4795_; 
v_vs_4761_ = lean_ctor_get(v_n_4724_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v_n_4724_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4763_ = v_n_4724_;
v_isShared_4764_ = v_isSharedCheck_4795_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_vs_4761_);
lean_dec(v_n_4724_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4795_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; size_t v_sz_4767_; size_t v___x_4768_; lean_object* v___x_4769_; 
v___x_4765_ = lean_box(0);
v___x_4766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4765_);
lean_ctor_set(v___x_4766_, 1, v_b_4725_);
v_sz_4767_ = lean_array_size(v_vs_4761_);
v___x_4768_ = ((size_t)0ULL);
v___x_4769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_vs_4761_, v_sz_4767_, v___x_4768_, v___x_4766_);
lean_dec_ref(v_vs_4761_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4777_; 
lean_del_object(v___x_4763_);
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4772_ = v___x_4769_;
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4769_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4775_; 
if (v_isShared_4773_ == 0)
{
v___x_4775_ = v___x_4772_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4770_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4794_; 
v_a_4778_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4780_ = v___x_4769_;
v_isShared_4781_ = v_isSharedCheck_4794_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4769_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4794_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v_fst_4782_; 
v_fst_4782_ = lean_ctor_get(v_a_4778_, 0);
if (lean_obj_tag(v_fst_4782_) == 0)
{
lean_object* v_snd_4783_; lean_object* v___x_4785_; 
v_snd_4783_ = lean_ctor_get(v_a_4778_, 1);
lean_inc(v_snd_4783_);
lean_dec(v_a_4778_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 0, v_snd_4783_);
v___x_4785_ = v___x_4763_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_snd_4783_);
v___x_4785_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
lean_object* v___x_4787_; 
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v___x_4785_);
v___x_4787_ = v___x_4780_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4785_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
else
{
lean_object* v_val_4790_; lean_object* v___x_4792_; 
lean_inc_ref(v_fst_4782_);
lean_dec(v_a_4778_);
lean_del_object(v___x_4763_);
v_val_4790_ = lean_ctor_get(v_fst_4782_, 0);
lean_inc(v_val_4790_);
lean_dec_ref(v_fst_4782_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v_val_4790_);
v___x_4792_ = v___x_4780_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_val_4790_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object* v_inh_4796_, lean_object* v_as_4797_, size_t v_sz_4798_, size_t v_i_4799_, lean_object* v_b_4800_){
_start:
{
uint8_t v___x_4801_; 
v___x_4801_ = lean_usize_dec_lt(v_i_4799_, v_sz_4798_);
if (v___x_4801_ == 0)
{
lean_object* v___x_4802_; 
v___x_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4802_, 0, v_b_4800_);
return v___x_4802_;
}
else
{
lean_object* v_snd_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4837_; 
v_snd_4803_ = lean_ctor_get(v_b_4800_, 1);
v_isSharedCheck_4837_ = !lean_is_exclusive(v_b_4800_);
if (v_isSharedCheck_4837_ == 0)
{
lean_object* v_unused_4838_; 
v_unused_4838_ = lean_ctor_get(v_b_4800_, 0);
lean_dec(v_unused_4838_);
v___x_4805_ = v_b_4800_;
v_isShared_4806_ = v_isSharedCheck_4837_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_snd_4803_);
lean_dec(v_b_4800_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4837_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v_a_4807_; lean_object* v___x_4808_; 
v_a_4807_ = lean_array_uget_borrowed(v_as_4797_, v_i_4799_);
lean_inc(v_snd_4803_);
lean_inc(v_a_4807_);
v___x_4808_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_inh_4796_, v_a_4807_, v_snd_4803_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v_a_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4816_; 
lean_del_object(v___x_4805_);
lean_dec(v_snd_4803_);
v_a_4809_ = lean_ctor_get(v___x_4808_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4808_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4811_ = v___x_4808_;
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4808_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4814_; 
if (v_isShared_4812_ == 0)
{
v___x_4814_ = v___x_4811_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_a_4809_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
else
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4836_; 
v_a_4817_ = lean_ctor_get(v___x_4808_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4808_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4819_ = v___x_4808_;
v_isShared_4820_ = v_isSharedCheck_4836_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4808_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4836_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
if (lean_obj_tag(v_a_4817_) == 0)
{
lean_object* v___x_4821_; lean_object* v___x_4823_; 
v___x_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4821_, 0, v_a_4817_);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 0, v___x_4821_);
v___x_4823_ = v___x_4805_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v___x_4821_);
lean_ctor_set(v_reuseFailAlloc_4827_, 1, v_snd_4803_);
v___x_4823_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
lean_object* v___x_4825_; 
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 0, v___x_4823_);
v___x_4825_ = v___x_4819_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4823_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4829_; lean_object* v___x_4831_; 
lean_del_object(v___x_4819_);
lean_dec(v_snd_4803_);
v_a_4828_ = lean_ctor_get(v_a_4817_, 0);
lean_inc(v_a_4828_);
lean_dec_ref(v_a_4817_);
v___x_4829_ = lean_box(0);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 1, v_a_4828_);
lean_ctor_set(v___x_4805_, 0, v___x_4829_);
v___x_4831_ = v___x_4805_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4829_);
lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_a_4828_);
v___x_4831_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
size_t v___x_4832_; size_t v___x_4833_; 
v___x_4832_ = ((size_t)1ULL);
v___x_4833_ = lean_usize_add(v_i_4799_, v___x_4832_);
v_i_4799_ = v___x_4833_;
v_b_4800_ = v___x_4831_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object* v_inh_4839_, lean_object* v_as_4840_, lean_object* v_sz_4841_, lean_object* v_i_4842_, lean_object* v_b_4843_){
_start:
{
size_t v_sz_boxed_4844_; size_t v_i_boxed_4845_; lean_object* v_res_4846_; 
v_sz_boxed_4844_ = lean_unbox_usize(v_sz_4841_);
lean_dec(v_sz_4841_);
v_i_boxed_4845_ = lean_unbox_usize(v_i_4842_);
lean_dec(v_i_4842_);
v_res_4846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_inh_4839_, v_as_4840_, v_sz_boxed_4844_, v_i_boxed_4845_, v_b_4843_);
lean_dec_ref(v_as_4840_);
lean_dec_ref(v_inh_4839_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object* v_inh_4847_, lean_object* v_n_4848_, lean_object* v_b_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_inh_4847_, v_n_4848_, v_b_4849_);
lean_dec_ref(v_inh_4847_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object* v_t_4851_, lean_object* v_init_4852_){
_start:
{
lean_object* v_root_4853_; lean_object* v_tail_4854_; lean_object* v___x_4855_; 
v_root_4853_ = lean_ctor_get(v_t_4851_, 0);
lean_inc_ref(v_root_4853_);
v_tail_4854_ = lean_ctor_get(v_t_4851_, 1);
lean_inc_ref(v_tail_4854_);
lean_dec_ref(v_t_4851_);
lean_inc_ref(v_init_4852_);
v___x_4855_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4852_, v_root_4853_, v_init_4852_);
lean_dec_ref(v_init_4852_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
lean_dec_ref(v_tail_4854_);
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4855_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4855_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4900_; 
v_a_4864_ = lean_ctor_get(v___x_4855_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4866_ = v___x_4855_;
v_isShared_4867_ = v_isSharedCheck_4900_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4855_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4900_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
if (lean_obj_tag(v_a_4864_) == 0)
{
lean_object* v_a_4868_; lean_object* v___x_4870_; 
lean_dec_ref(v_tail_4854_);
v_a_4868_ = lean_ctor_get(v_a_4864_, 0);
lean_inc(v_a_4868_);
lean_dec_ref(v_a_4864_);
if (v_isShared_4867_ == 0)
{
lean_ctor_set(v___x_4866_, 0, v_a_4868_);
v___x_4870_ = v___x_4866_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4868_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
else
{
lean_object* v_a_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; size_t v_sz_4875_; size_t v___x_4876_; lean_object* v___x_4877_; 
lean_del_object(v___x_4866_);
v_a_4872_ = lean_ctor_get(v_a_4864_, 0);
lean_inc(v_a_4872_);
lean_dec_ref(v_a_4864_);
v___x_4873_ = lean_box(0);
v___x_4874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4873_);
lean_ctor_set(v___x_4874_, 1, v_a_4872_);
v_sz_4875_ = lean_array_size(v_tail_4854_);
v___x_4876_ = ((size_t)0ULL);
v___x_4877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_tail_4854_, v_sz_4875_, v___x_4876_, v___x_4874_);
lean_dec_ref(v_tail_4854_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4885_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4880_ = v___x_4877_;
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4877_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4883_; 
if (v_isShared_4881_ == 0)
{
v___x_4883_ = v___x_4880_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_a_4878_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
else
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4899_; 
v_a_4886_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4888_ = v___x_4877_;
v_isShared_4889_ = v_isSharedCheck_4899_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4877_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4899_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v_fst_4890_; 
v_fst_4890_ = lean_ctor_get(v_a_4886_, 0);
if (lean_obj_tag(v_fst_4890_) == 0)
{
lean_object* v_snd_4891_; lean_object* v___x_4893_; 
v_snd_4891_ = lean_ctor_get(v_a_4886_, 1);
lean_inc(v_snd_4891_);
lean_dec(v_a_4886_);
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 0, v_snd_4891_);
v___x_4893_ = v___x_4888_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_snd_4891_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
else
{
lean_object* v_val_4895_; lean_object* v___x_4897_; 
lean_inc_ref(v_fst_4890_);
lean_dec(v_a_4886_);
v_val_4895_ = lean_ctor_get(v_fst_4890_, 0);
lean_inc(v_val_4895_);
lean_dec_ref(v_fst_4890_);
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 0, v_val_4895_);
v___x_4897_ = v___x_4888_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_val_4895_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_assemble___closed__1(void){
_start:
{
lean_object* v___x_4903_; lean_object* v_ctx_4904_; 
v___x_4903_ = ((lean_object*)(l_Lean_VersoModuleDocs_assemble___closed__0));
v_ctx_4904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctx_4904_, 0, v___x_4903_);
lean_ctor_set(v_ctx_4904_, 1, v___x_4903_);
lean_ctor_set(v_ctx_4904_, 2, v___x_4903_);
return v_ctx_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object* v_docs_4905_){
_start:
{
lean_object* v_snippets_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4943_; 
v_snippets_4906_ = lean_ctor_get(v_docs_4905_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v_docs_4905_);
if (v_isSharedCheck_4943_ == 0)
{
lean_object* v_unused_4944_; 
v_unused_4944_ = lean_ctor_get(v_docs_4905_, 1);
lean_dec(v_unused_4944_);
v___x_4908_ = v_docs_4905_;
v_isShared_4909_ = v_isSharedCheck_4943_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_snippets_4906_);
lean_dec(v_docs_4905_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4943_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v_ctx_4910_; lean_object* v___x_4911_; 
v_ctx_4910_ = lean_obj_once(&l_Lean_VersoModuleDocs_assemble___closed__1, &l_Lean_VersoModuleDocs_assemble___closed__1_once, _init_l_Lean_VersoModuleDocs_assemble___closed__1);
v___x_4911_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_snippets_4906_, v_ctx_4910_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4919_; 
lean_del_object(v___x_4908_);
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4914_ = v___x_4911_;
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4911_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4917_; 
if (v_isShared_4915_ == 0)
{
v___x_4917_ = v___x_4914_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4912_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
else
{
lean_object* v_a_4920_; lean_object* v___x_4921_; 
v_a_4920_ = lean_ctor_get(v___x_4911_, 0);
lean_inc(v_a_4920_);
lean_dec_ref(v___x_4911_);
v___x_4921_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(v_a_4920_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4929_; 
lean_del_object(v___x_4908_);
v_a_4922_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4924_ = v___x_4921_;
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4921_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4942_; 
v_a_4930_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4932_ = v___x_4921_;
v_isShared_4933_ = v_isSharedCheck_4942_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4921_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4942_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v_content_4934_; lean_object* v_priorParts_4935_; lean_object* v___x_4937_; 
v_content_4934_ = lean_ctor_get(v_a_4930_, 0);
lean_inc_ref(v_content_4934_);
v_priorParts_4935_ = lean_ctor_get(v_a_4930_, 1);
lean_inc_ref(v_priorParts_4935_);
lean_dec(v_a_4930_);
if (v_isShared_4909_ == 0)
{
lean_ctor_set(v___x_4908_, 1, v_priorParts_4935_);
lean_ctor_set(v___x_4908_, 0, v_content_4934_);
v___x_4937_ = v___x_4908_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_content_4934_);
lean_ctor_set(v_reuseFailAlloc_4941_, 1, v_priorParts_4935_);
v___x_4937_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
lean_object* v___x_4939_; 
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4937_);
v___x_4939_ = v___x_4932_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v___x_4937_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object* v_x_4947_, lean_object* v_x_4948_, lean_object* v_es_4949_, uint8_t v_level_4950_){
_start:
{
uint8_t v___x_4951_; uint8_t v___x_4952_; 
v___x_4951_ = 1;
v___x_4952_ = l_Lean_instOrdOLeanLevel_ord(v_level_4950_, v___x_4951_);
if (v___x_4952_ == 0)
{
lean_object* v___x_4953_; 
lean_dec(v_es_4949_);
v___x_4953_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_));
return v___x_4953_;
}
else
{
lean_object* v___x_4954_; 
v___x_4954_ = lean_array_mk(v_es_4949_);
return v___x_4954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object* v_x_4955_, lean_object* v_x_4956_, lean_object* v_es_4957_, lean_object* v_level_4958_){
_start:
{
uint8_t v_level_boxed_4959_; lean_object* v_res_4960_; 
v_level_boxed_4959_ = lean_unbox(v_level_4958_);
v_res_4960_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(v_x_4955_, v_x_4956_, v_es_4957_, v_level_boxed_4959_);
lean_dec_ref(v_x_4956_);
lean_dec_ref(v_x_4955_);
return v_res_4960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object* v_es_4961_){
_start:
{
lean_object* v___x_4962_; 
v___x_4962_ = lean_array_mk(v_es_4961_);
return v___x_4962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_4963_, lean_object* v_i_4964_){
_start:
{
lean_object* v_zero_4965_; uint8_t v_isZero_4966_; 
v_zero_4965_ = lean_unsigned_to_nat(0u);
v_isZero_4966_ = lean_nat_dec_eq(v_i_4964_, v_zero_4965_);
if (v_isZero_4966_ == 1)
{
lean_object* v___x_4967_; 
lean_dec(v_i_4964_);
v___x_4967_ = lean_box(0);
return v___x_4967_;
}
else
{
lean_object* v_one_4968_; lean_object* v_n_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v_one_4968_ = lean_unsigned_to_nat(1u);
v_n_4969_ = lean_nat_sub(v_i_4964_, v_one_4968_);
lean_dec(v_i_4964_);
v___x_4970_ = lean_array_fget_borrowed(v_as_4963_, v_n_4969_);
v___x_4971_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v___x_4970_);
if (lean_obj_tag(v___x_4971_) == 0)
{
v_i_4964_ = v_n_4969_;
goto _start;
}
else
{
lean_dec(v_n_4969_);
return v___x_4971_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_4973_, lean_object* v_i_4974_){
_start:
{
lean_object* v_res_4975_; 
v_res_4975_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4973_, v_i_4974_);
lean_dec_ref(v_as_4973_);
return v_res_4975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_as_4976_, lean_object* v_i_4977_){
_start:
{
lean_object* v_zero_4978_; uint8_t v_isZero_4979_; 
v_zero_4978_ = lean_unsigned_to_nat(0u);
v_isZero_4979_ = lean_nat_dec_eq(v_i_4977_, v_zero_4978_);
if (v_isZero_4979_ == 1)
{
lean_object* v___x_4980_; 
lean_dec(v_i_4977_);
v___x_4980_ = lean_box(0);
return v___x_4980_;
}
else
{
lean_object* v_one_4981_; lean_object* v_n_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v_one_4981_ = lean_unsigned_to_nat(1u);
v_n_4982_ = lean_nat_sub(v_i_4977_, v_one_4981_);
lean_dec(v_i_4977_);
v___x_4983_ = lean_array_fget_borrowed(v_as_4976_, v_n_4982_);
v___x_4984_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(v___x_4983_);
if (lean_obj_tag(v___x_4984_) == 0)
{
v_i_4977_ = v_n_4982_;
goto _start;
}
else
{
lean_dec(v_n_4982_);
return v___x_4984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_x_4986_){
_start:
{
if (lean_obj_tag(v_x_4986_) == 0)
{
lean_object* v_cs_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v_cs_4987_ = lean_ctor_get(v_x_4986_, 0);
v___x_4988_ = lean_array_get_size(v_cs_4987_);
v___x_4989_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_cs_4987_, v___x_4988_);
return v___x_4989_;
}
else
{
lean_object* v_vs_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v_vs_4990_ = lean_ctor_get(v_x_4986_, 0);
v___x_4991_ = lean_array_get_size(v_vs_4990_);
v___x_4992_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_vs_4990_, v___x_4991_);
return v___x_4992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_x_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(v_x_4993_);
lean_dec_ref(v_x_4993_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_4995_, lean_object* v_i_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_as_4995_, v_i_4996_);
lean_dec_ref(v_as_4995_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0(lean_object* v_t_4998_){
_start:
{
lean_object* v_root_4999_; lean_object* v_tail_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v_root_4999_ = lean_ctor_get(v_t_4998_, 0);
v_tail_5000_ = lean_ctor_get(v_t_4998_, 1);
v___x_5001_ = lean_array_get_size(v_tail_5000_);
v___x_5002_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_tail_5000_, v___x_5001_);
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_object* v___x_5003_; 
v___x_5003_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(v_root_4999_);
return v___x_5003_;
}
else
{
return v___x_5002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0___boxed(lean_object* v_t_5004_){
_start:
{
lean_object* v_res_5005_; 
v_res_5005_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0(v_t_5004_);
lean_dec_ref(v_t_5004_);
return v_res_5005_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
v___x_5006_ = lean_unsigned_to_nat(32u);
v___x_5007_ = lean_mk_empty_array_with_capacity(v___x_5006_);
v___x_5008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5008_, 0, v___x_5007_);
return v___x_5008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object* v___x_5009_, lean_object* v_x_5010_){
_start:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; size_t v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5011_ = lean_unsigned_to_nat(32u);
v___x_5012_ = lean_mk_empty_array_with_capacity(v___x_5011_);
v___x_5013_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_);
v___x_5014_ = ((size_t)5ULL);
lean_inc(v___x_5009_);
v___x_5015_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5015_, 0, v___x_5013_);
lean_ctor_set(v___x_5015_, 1, v___x_5012_);
lean_ctor_set(v___x_5015_, 2, v___x_5009_);
lean_ctor_set(v___x_5015_, 3, v___x_5009_);
lean_ctor_set_usize(v___x_5015_, 4, v___x_5014_);
v___x_5016_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0(v___x_5015_);
v___x_5017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5015_);
lean_ctor_set(v___x_5017_, 1, v___x_5016_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object* v___x_5018_, lean_object* v_x_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(v___x_5018_, v_x_5019_);
lean_dec_ref(v_x_5019_);
return v_res_5020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5041_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_));
v___x_5042_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5041_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object* v_a_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_();
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_5045_, lean_object* v_i_5046_, lean_object* v_a_5047_){
_start:
{
lean_object* v___x_5048_; 
v___x_5048_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_5045_, v_i_5046_);
return v___x_5048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_5049_, lean_object* v_i_5050_, lean_object* v_a_5051_){
_start:
{
lean_object* v_res_5052_; 
v_res_5052_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0(v_as_5049_, v_i_5050_, v_a_5051_);
lean_dec_ref(v_as_5049_);
return v_res_5052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_as_5053_, lean_object* v_i_5054_, lean_object* v_a_5055_){
_start:
{
lean_object* v___x_5056_; 
v___x_5056_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_as_5053_, v_i_5054_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___boxed(lean_object* v_as_5057_, lean_object* v_i_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2(v_as_5057_, v_i_5058_, v_a_5059_);
lean_dec_ref(v_as_5057_);
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object* v_env_5061_){
_start:
{
lean_object* v___x_5062_; lean_object* v_toEnvExtension_5063_; lean_object* v_asyncMode_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5062_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc_ref(v_toEnvExtension_5063_);
v_asyncMode_5064_ = lean_ctor_get(v_toEnvExtension_5063_, 2);
lean_inc(v_asyncMode_5064_);
lean_dec_ref(v_toEnvExtension_5063_);
v___x_5065_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_5066_ = lean_box(0);
v___x_5067_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5065_, v___x_5062_, v_env_5061_, v_asyncMode_5064_, v___x_5066_);
lean_dec(v_asyncMode_5064_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object* v_env_5068_){
_start:
{
lean_object* v___x_5069_; 
v___x_5069_ = l_Lean_getMainVersoModuleDocs(v_env_5068_);
return v___x_5069_;
}
}
static lean_object* _init_l_Lean_getVersoModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5070_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_5071_ = lean_box(0);
v___x_5072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5071_);
lean_ctor_set(v___x_5072_, 1, v___x_5070_);
return v___x_5072_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object* v_env_5073_, lean_object* v_moduleName_5074_){
_start:
{
lean_object* v___x_5075_; 
v___x_5075_ = l_Lean_Environment_getModuleIdx_x3f(v_env_5073_, v_moduleName_5074_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_object* v___x_5076_; 
v___x_5076_ = lean_box(0);
return v___x_5076_;
}
else
{
lean_object* v_val_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5088_; 
v_val_5077_ = lean_ctor_get(v___x_5075_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5079_ = v___x_5075_;
v_isShared_5080_ = v_isSharedCheck_5088_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_val_5077_);
lean_dec(v___x_5075_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5088_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; uint8_t v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5086_; 
v___x_5081_ = lean_obj_once(&l_Lean_getVersoModuleDoc_x3f___closed__0, &l_Lean_getVersoModuleDoc_x3f___closed__0_once, _init_l_Lean_getVersoModuleDoc_x3f___closed__0);
v___x_5082_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v___x_5083_ = 1;
v___x_5084_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_5081_, v___x_5082_, v_env_5073_, v_val_5077_, v___x_5083_);
lean_dec(v_val_5077_);
if (v_isShared_5080_ == 0)
{
lean_ctor_set(v___x_5079_, 0, v___x_5084_);
v___x_5086_ = v___x_5079_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v___x_5084_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object* v_env_5089_, lean_object* v_moduleName_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l_Lean_getVersoModuleDoc_x3f(v_env_5089_, v_moduleName_5090_);
lean_dec(v_moduleName_5090_);
lean_dec_ref(v_env_5089_);
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object* v_env_5094_, lean_object* v_snippet_5095_){
_start:
{
lean_object* v_docs_5096_; uint8_t v___x_5097_; 
lean_inc_ref(v_env_5094_);
v_docs_5096_ = l_Lean_getMainVersoModuleDocs(v_env_5094_);
v___x_5097_ = l_Lean_VersoModuleDocs_canAdd(v_docs_5096_, v_snippet_5095_);
if (v___x_5097_ == 0)
{
lean_object* v_terminalNesting_5098_; lean_object* v___x_5099_; lean_object* v___y_5101_; 
lean_dec_ref(v_snippet_5095_);
lean_dec_ref(v_env_5094_);
v_terminalNesting_5098_ = lean_ctor_get(v_docs_5096_, 1);
lean_inc(v_terminalNesting_5098_);
lean_dec_ref(v_docs_5096_);
v___x_5099_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__0));
if (lean_obj_tag(v_terminalNesting_5098_) == 0)
{
lean_object* v___x_5106_; 
v___x_5106_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___y_5101_ = v___x_5106_;
goto v___jp_5100_;
}
else
{
lean_object* v_val_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; 
v_val_5107_ = lean_ctor_get(v_terminalNesting_5098_, 0);
lean_inc(v_val_5107_);
lean_dec_ref(v_terminalNesting_5098_);
v___x_5108_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__1));
v___x_5109_ = l_Nat_reprFast(v_val_5107_);
v___x_5110_ = lean_string_append(v___x_5108_, v___x_5109_);
lean_dec_ref(v___x_5109_);
v___x_5111_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_5112_ = lean_string_append(v___x_5110_, v___x_5111_);
v___y_5101_ = v___x_5112_;
goto v___jp_5100_;
}
v___jp_5100_:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5102_ = lean_string_append(v___x_5099_, v___y_5101_);
lean_dec_ref(v___y_5101_);
v___x_5103_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_5104_ = lean_string_append(v___x_5102_, v___x_5103_);
v___x_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
return v___x_5105_;
}
}
else
{
lean_object* v___x_5113_; lean_object* v_toEnvExtension_5114_; lean_object* v_asyncMode_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; 
lean_dec_ref(v_docs_5096_);
v___x_5113_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_5114_ = lean_ctor_get(v___x_5113_, 0);
lean_inc_ref(v_toEnvExtension_5114_);
v_asyncMode_5115_ = lean_ctor_get(v_toEnvExtension_5114_, 2);
lean_inc(v_asyncMode_5115_);
lean_dec_ref(v_toEnvExtension_5114_);
v___x_5116_ = lean_box(0);
v___x_5117_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5113_, v_env_5094_, v_snippet_5095_, v_asyncMode_5115_, v___x_5116_);
lean_dec(v_asyncMode_5115_);
v___x_5118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5118_, 0, v___x_5117_);
return v___x_5118_;
}
}
}
lean_object* runtime_initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Markdown(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instMarkdownInlineElabInline = _init_l_Lean_instMarkdownInlineElabInline();
lean_mark_persistent(l_Lean_instMarkdownInlineElabInline);
l_Lean_instMarkdownBlockElabInlineElabBlock = _init_l_Lean_instMarkdownBlockElabInlineElabBlock();
lean_mark_persistent(l_Lean_instMarkdownBlockElabInlineElabBlock);
l_Lean_instInhabitedVersoDocString_default = _init_l_Lean_instInhabitedVersoDocString_default();
lean_mark_persistent(l_Lean_instInhabitedVersoDocString_default);
l_Lean_instInhabitedVersoDocString = _init_l_Lean_instInhabitedVersoDocString();
lean_mark_persistent(l_Lean_instInhabitedVersoDocString);
res = l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_doc_verso = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_doc_verso);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_doc_verso_module = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_doc_verso_module);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_docStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_docStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_versoDocStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_versoDocStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_moduleDocExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_moduleDocExt);
lean_dec_ref(res);
l_Lean_VersoModuleDocs_instInhabitedSnippet_default = _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default();
lean_mark_persistent(l_Lean_VersoModuleDocs_instInhabitedSnippet_default);
l_Lean_VersoModuleDocs_instInhabitedSnippet = _init_l_Lean_VersoModuleDocs_instInhabitedSnippet();
lean_mark_persistent(l_Lean_VersoModuleDocs_instInhabitedSnippet);
l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1 = _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1();
lean_mark_persistent(l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1);
l_Lean_instToMarkdownSnippet = _init_l_Lean_instToMarkdownSnippet();
lean_mark_persistent(l_Lean_instToMarkdownSnippet);
l_Lean_instInhabitedVersoModuleDocs_default = _init_l_Lean_instInhabitedVersoModuleDocs_default();
lean_mark_persistent(l_Lean_instInhabitedVersoModuleDocs_default);
l_Lean_instInhabitedVersoModuleDocs = _init_l_Lean_instInhabitedVersoModuleDocs();
lean_mark_persistent(l_Lean_instInhabitedVersoModuleDocs);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_();
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
lean_object* initialize_Lean_DocString_Markdown(uint8_t builtin);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Extension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin);
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
