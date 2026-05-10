// Lean compiler output
// Module: Lean.Util.Trace
// Imports: public import Lean.Elab.Exception public import Lean.Log
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
lean_object* l_MonadExcept_ofExcept___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_KVMap_instValueNat;
double lean_float_div(double, double);
lean_object* l_IO_monoNanosNow___boxed(lean_object*);
lean_object* l_IO_getNumHeartbeats___boxed(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonadExceptOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
lean_object* l_Lean_MessageData_format___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BaseIO_toIO___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueString;
lean_object* l_Lean_Option_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_instToStringFormat___lam__0(lean_object*);
lean_object* l_IO_println___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqRaw___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_instHashableRaw_hash___boxed(lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_StateT_instMonadExceptOf___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonadExceptOf___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedTraceElem_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTraceElem_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceElem_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceElem;
static lean_once_cell_t l_Lean_instInhabitedTraceState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTraceState_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedTraceState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTraceState_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedTraceState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTraceState_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceState_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceState;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_inheritedTraceOptions;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value;
static const lean_array_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "inheritedTraceOptions.get"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14_value;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "inheritedTraceOptions"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value),LEAN_SCALAR_PTR_LITERAL(111, 221, 127, 62, 213, 113, 62, 253)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value),LEAN_SCALAR_PTR_LITERAL(249, 53, 178, 254, 160, 90, 192, 243)}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28;
LEAN_EXPORT lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam;
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_printTraces___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringFormat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_printTraces___redArg___closed__0 = (const lean_object*)&l_Lean_printTraces___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_resetTraceState___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_resetTraceState___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resetTraceState___redArg___closed__0 = (const lean_object*)&l_Lean_resetTraceState___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resetTraceState(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkTraceOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_checkTraceOption___closed__0 = (const lean_object*)&l_Lean_checkTraceOption___closed__0_value;
static const lean_ctor_object l_Lean_checkTraceOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_checkTraceOption___closed__1 = (const lean_object*)&l_Lean_checkTraceOption___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkTraceOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_is_trace_class_enabled(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___redArg___lam__0___closed__0;
static const lean_string_object l_Lean_addTrace___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_addTrace___redArg___lam__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_addTrace___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "profiler"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "activate nested traces with execution time above `trace.profiler.threshold` and annotate with time"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "threshold"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(184, 9, 42, 114, 12, 38, 11, 42)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 130, .m_capacity = 130, .m_length = 129, .m_data = "threshold in milliseconds (or heartbeats if `trace.profiler.useHeartbeats` is true), traces below threshold will not be activated"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 45, 177, 27, 189, 220, 1, 137)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "useHeartbeats"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 182, 122, 179, 202, 46, 182, 49)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "if true, measure and report heartbeats instead of seconds"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(89, 248, 181, 172, 128, 194, 123, 56)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_useHeartbeats;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "output"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(19, 45, 221, 139, 23, 193, 130, 68)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "output `trace.profiler` data in Firefox Profiler-compatible format to given file path"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addTrace___redArg___lam__0___closed__1_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(58, 195, 204, 148, 25, 40, 60, 227)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_output;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "serve"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(178, 232, 14, 81, 31, 251, 216, 133)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "serve the `trace.profiler` data over HTTP and open it in `https://profiler.firefox.com`; blocks until interrupted with Ctrl+C"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(43, 90, 16, 252, 133, 113, 145, 70)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_serve;
LEAN_EXPORT uint8_t l_Lean_trace_profiler_isExporting(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_isExporting___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(19, 45, 221, 139, 23, 193, 130, 68)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(193, 225, 100, 102, 84, 233, 134, 170)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 232, .m_capacity = 232, .m_length = 231, .m_data = "if false, limit text in exported trace nodes to trace class name and `TraceData.tag`, if any\n\nThis is useful when we are interested in the time taken by specific subsystems instead of specific invocations, which is the common case."};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(58, 195, 204, 148, 25, 40, 60, 227)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(228, 86, 200, 244, 100, 192, 149, 216)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_output_pp;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_monoNanosNow___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_getNumHeartbeats___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_trace_profiler_threshold_unitAdjusted___closed__0;
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object*);
static lean_once_cell_t l_Lean_instMonadAlwaysExceptEIO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instMonadAlwaysExceptEIO___closed__0;
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_bombEmoji___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 2, .m_data = "💥️"};
static const lean_object* l_Lean_bombEmoji___closed__0 = (const lean_object*)&l_Lean_bombEmoji___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_bombEmoji = (const lean_object*)&l_Lean_bombEmoji___closed__0_value;
static const lean_string_object l_Lean_checkEmoji___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 2, .m_data = "✅️"};
static const lean_object* l_Lean_checkEmoji___closed__0 = (const lean_object*)&l_Lean_checkEmoji___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_checkEmoji = (const lean_object*)&l_Lean_checkEmoji___closed__0_value;
static const lean_string_object l_Lean_crossEmoji___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 2, .m_data = "❌️"};
static const lean_object* l_Lean_crossEmoji___closed__0 = (const lean_object*)&l_Lean_crossEmoji___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_crossEmoji = (const lean_object*)&l_Lean_crossEmoji___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResultBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResultBool___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResultBool___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResultOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultOption___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResultOption___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResultOption___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResult___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResult___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResult___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, double, double, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object**);
static const lean_closure_object l_Lean_withTraceNode_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withTraceNode_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_withTraceNode_x27___redArg___closed__0 = (const lean_object*)&l_Lean_withTraceNode_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerTraceClass___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_registerTraceClass___auto__1___closed__0 = (const lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value;
static const lean_string_object l_Lean_registerTraceClass___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_registerTraceClass___auto__1___closed__1 = (const lean_object*)&l_Lean_registerTraceClass___auto__1___closed__1_value;
static const lean_ctor_object l_Lean_registerTraceClass___auto__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_registerTraceClass___auto__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__2_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_registerTraceClass___auto__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__2_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_registerTraceClass___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__2_value_aux_2),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_registerTraceClass___auto__1___closed__2 = (const lean_object*)&l_Lean_registerTraceClass___auto__1___closed__2_value;
static const lean_string_object l_Lean_registerTraceClass___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_registerTraceClass___auto__1___closed__3 = (const lean_object*)&l_Lean_registerTraceClass___auto__1___closed__3_value;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__4;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__5;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__6;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__7;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__8;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__9;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__10;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__11;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__12;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__13;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__14;
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___auto__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_registerTraceClass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_registerTraceClass___closed__0 = (const lean_object*)&l_Lean_registerTraceClass___closed__0_value;
static const lean_string_object l_Lean_registerTraceClass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "enable/disable tracing for the given module and submodules"};
static const lean_object* l_Lean_registerTraceClass___closed__1 = (const lean_object*)&l_Lean_registerTraceClass___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "liftMethod"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.isTracingEnabledFor"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "isTracingEnabledFor"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.addTrace"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "addTrace"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cls"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value),LEAN_SCALAR_PTR_LITERAL(28, 113, 141, 155, 240, 79, 69, 244)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MessageData"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value),LEAN_SCALAR_PTR_LITERAL(117, 193, 162, 252, 67, 31, 191, 159)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doElemTrace[_]__"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__0 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value_aux_0),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 144, 171, 160, 60, 151, 54, 39)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__1 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__2 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__3 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "trace["};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__4 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__5 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__6 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__7 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__8 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__9 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__10 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__11 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__12 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__13 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__14 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__15 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__16 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__17 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__18 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__19 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__20 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__21 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__22 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__23 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value;
LEAN_EXPORT const lean_object* l_Lean_doElemTrace_x5b___x5d____ = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value;
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__0;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__1;
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHashableRaw_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__2 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value;
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___lam__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableProd___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value),((lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value)} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__3 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__11___closed__3_value;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__4;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__5;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_addTraceAsMessages___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___closed__0 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___closed__0_value;
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_addTraceAsMessages___redArg___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___closed__1 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 215, 222, 176, 152, 52, 0, 225)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 20, 155, 62, 160, 30, 19, 156)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Trace"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 45, 197, 3, 218, 39, 236, 122)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(212, 132, 182, 134, 118, 170, 212, 125)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 109, 156, 246, 253, 156, 207, 235)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(252, 109, 61, 254, 212, 130, 102, 57)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 63, 132, 83, 234, 34, 87, 212)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 141, 129, 211, 167, 99, 91, 102)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 185, 91, 65, 254, 191, 29, 193)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 72, 204, 88, 19, 210, 210, 71)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_instInhabitedTraceElem_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = l_Lean_instInhabitedMessageData_default;
v___x_2_ = lean_box(0);
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceElem_default(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&l_Lean_instInhabitedTraceElem_default___closed__0, &l_Lean_instInhabitedTraceElem_default___closed__0_once, _init_l_Lean_instInhabitedTraceElem_default___closed__0);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceElem(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Lean_instInhabitedTraceElem_default;
return v___x_5_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState_default___closed__0(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_unsigned_to_nat(32u);
v___x_7_ = lean_mk_empty_array_with_capacity(v___x_6_);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState_default___closed__1(void){
_start:
{
size_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_9_ = ((size_t)5ULL);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_unsigned_to_nat(32u);
v___x_12_ = lean_mk_empty_array_with_capacity(v___x_11_);
v___x_13_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__0, &l_Lean_instInhabitedTraceState_default___closed__0_once, _init_l_Lean_instInhabitedTraceState_default___closed__0);
v___x_14_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
lean_ctor_set(v___x_14_, 2, v___x_10_);
lean_ctor_set(v___x_14_, 3, v___x_10_);
lean_ctor_set_usize(v___x_14_, 4, v___x_9_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState_default___closed__2(void){
_start:
{
lean_object* v___x_15_; uint64_t v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__1, &l_Lean_instInhabitedTraceState_default___closed__1_once, _init_l_Lean_instInhabitedTraceState_default___closed__1);
v___x_16_ = 0ULL;
v___x_17_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_17_, 0, v___x_15_);
lean_ctor_set_uint64(v___x_17_, sizeof(void*)*1, v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState_default(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__2, &l_Lean_instInhabitedTraceState_default___closed__2_once, _init_l_Lean_instInhabitedTraceState_default___closed__2);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_instInhabitedTraceState_default;
return v___x_19_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_20_ = lean_box(0);
v___x_21_ = lean_unsigned_to_nat(16u);
v___x_22_ = lean_mk_array(v___x_21_, v___x_20_);
return v___x_22_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
v___x_24_ = lean_unsigned_to_nat(0u);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v___x_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
v___x_28_ = lean_st_mk_ref(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2____boxed(lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
return v_res_31_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10));
v___x_59_ = l_Lean_mkAtom(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12);
v___x_61_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14));
v___x_65_ = lean_string_utf8_byte_size(v___x_64_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14));
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_75_ = lean_box(0);
v___x_76_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19));
v___x_77_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16);
v___x_78_ = lean_box(2);
v___x_79_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_76_);
lean_ctor_set(v___x_79_, 3, v___x_75_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20);
v___x_81_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_82_ = lean_array_push(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21);
v___x_84_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_85_ = lean_box(2);
v___x_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22);
v___x_88_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_89_ = lean_array_push(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23);
v___x_91_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_92_ = lean_box(2);
v___x_93_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
lean_ctor_set(v___x_93_, 2, v___x_90_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24);
v___x_95_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_96_ = lean_array_push(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25);
v___x_98_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_99_ = lean_box(2);
v___x_100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_97_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26);
v___x_102_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_103_ = lean_array_push(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27);
v___x_105_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_106_ = lean_box(2);
v___x_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_104_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg___lam__0(lean_object* v_modifyTraceState_109_, lean_object* v_inst_110_, lean_object* v_f_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_apply_1(v_modifyTraceState_109_, v_f_111_);
v___x_113_ = lean_apply_2(v_inst_110_, lean_box(0), v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object* v_inst_114_, lean_object* v_inst_115_){
_start:
{
lean_object* v_modifyTraceState_116_; lean_object* v_getTraceState_117_; lean_object* v_getInheritedTraceOptions_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_128_; 
v_modifyTraceState_116_ = lean_ctor_get(v_inst_115_, 0);
v_getTraceState_117_ = lean_ctor_get(v_inst_115_, 1);
v_getInheritedTraceOptions_118_ = lean_ctor_get(v_inst_115_, 2);
v_isSharedCheck_128_ = !lean_is_exclusive(v_inst_115_);
if (v_isSharedCheck_128_ == 0)
{
v___x_120_ = v_inst_115_;
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_getInheritedTraceOptions_118_);
lean_inc(v_getTraceState_117_);
lean_inc(v_modifyTraceState_116_);
lean_dec(v_inst_115_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___f_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
lean_inc_n(v_inst_114_, 2);
v___f_122_ = lean_alloc_closure((void*)(l_Lean_instMonadTraceOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_122_, 0, v_modifyTraceState_116_);
lean_closure_set(v___f_122_, 1, v_inst_114_);
v___x_123_ = lean_apply_2(v_inst_114_, lean_box(0), v_getTraceState_117_);
v___x_124_ = lean_apply_2(v_inst_114_, lean_box(0), v_getInheritedTraceOptions_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 2, v___x_124_);
lean_ctor_set(v___x_120_, 1, v___x_123_);
lean_ctor_set(v___x_120_, 0, v___f_122_);
v___x_126_ = v___x_120_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___f_122_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift(lean_object* v_m_129_, lean_object* v_n_130_, lean_object* v_inst_131_, lean_object* v_inst_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_instMonadTraceOfMonadLift___redArg(v_inst_131_, v_inst_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__0(lean_object* v_toPure_134_, lean_object* v_____s_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_box(0);
v___x_137_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__1(lean_object* v___x_138_, lean_object* v_toPure_139_, lean_object* v_r_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_138_);
v___x_142_ = lean_apply_2(v_toPure_139_, lean_box(0), v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__2(lean_object* v___f_143_, lean_object* v_inst_144_, lean_object* v_toBind_145_, lean_object* v___f_146_, lean_object* v_____do__lift_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_alloc_closure((void*)(l_IO_println___boxed), 4, 3);
lean_closure_set(v___x_148_, 0, lean_box(0));
lean_closure_set(v___x_148_, 1, v___f_143_);
lean_closure_set(v___x_148_, 2, v_____do__lift_147_);
v___x_149_ = lean_apply_2(v_inst_144_, lean_box(0), v___x_148_);
v___x_150_ = lean_apply_4(v_toBind_145_, lean_box(0), lean_box(0), v___x_149_, v___f_146_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__3(lean_object* v_inst_151_, lean_object* v_toBind_152_, lean_object* v___f_153_, lean_object* v_x_154_, lean_object* v_____s_155_){
_start:
{
lean_object* v_msg_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_msg_156_ = lean_ctor_get(v_x_154_, 1);
lean_inc_ref(v_msg_156_);
lean_dec_ref(v_x_154_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_alloc_closure((void*)(l_Lean_MessageData_format___boxed), 3, 2);
lean_closure_set(v___x_158_, 0, v_msg_156_);
lean_closure_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_alloc_closure((void*)(l_BaseIO_toIO___boxed), 3, 2);
lean_closure_set(v___x_159_, 0, lean_box(0));
lean_closure_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_apply_2(v_inst_151_, lean_box(0), v___x_159_);
v___x_161_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v___x_160_, v___f_153_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4(lean_object* v_toPure_162_, lean_object* v___f_163_, lean_object* v_inst_164_, lean_object* v_toBind_165_, lean_object* v_inst_166_, lean_object* v___f_167_, lean_object* v_____do__lift_168_){
_start:
{
lean_object* v_traces_169_; lean_object* v___x_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_traces_169_ = lean_ctor_get(v_____do__lift_168_, 0);
v___x_170_ = lean_box(0);
v___f_171_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_171_, 0, v___x_170_);
lean_closure_set(v___f_171_, 1, v_toPure_162_);
lean_inc_n(v_toBind_165_, 2);
lean_inc(v_inst_164_);
v___f_172_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_172_, 0, v___f_163_);
lean_closure_set(v___f_172_, 1, v_inst_164_);
lean_closure_set(v___f_172_, 2, v_toBind_165_);
lean_closure_set(v___f_172_, 3, v___f_171_);
v___f_173_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__3), 5, 3);
lean_closure_set(v___f_173_, 0, v_inst_164_);
lean_closure_set(v___f_173_, 1, v_toBind_165_);
lean_closure_set(v___f_173_, 2, v___f_172_);
v___x_174_ = l_Lean_PersistentArray_forIn___redArg(v_inst_166_, v_traces_169_, v___x_170_, v___f_173_);
v___x_175_ = lean_apply_4(v_toBind_165_, lean_box(0), lean_box(0), v___x_174_, v___f_167_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4___boxed(lean_object* v_toPure_176_, lean_object* v___f_177_, lean_object* v_inst_178_, lean_object* v_toBind_179_, lean_object* v_inst_180_, lean_object* v___f_181_, lean_object* v_____do__lift_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_printTraces___redArg___lam__4(v_toPure_176_, v___f_177_, v_inst_178_, v_toBind_179_, v_inst_180_, v___f_181_, v_____do__lift_182_);
lean_dec_ref(v_____do__lift_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg(lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_){
_start:
{
lean_object* v_toApplicative_188_; lean_object* v_toBind_189_; lean_object* v_getTraceState_190_; lean_object* v_toPure_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___x_195_; 
v_toApplicative_188_ = lean_ctor_get(v_inst_185_, 0);
v_toBind_189_ = lean_ctor_get(v_inst_185_, 1);
lean_inc_n(v_toBind_189_, 2);
v_getTraceState_190_ = lean_ctor_get(v_inst_186_, 1);
lean_inc(v_getTraceState_190_);
lean_dec_ref(v_inst_186_);
v_toPure_191_ = lean_ctor_get(v_toApplicative_188_, 1);
lean_inc_n(v_toPure_191_, 2);
v___f_192_ = ((lean_object*)(l_Lean_printTraces___redArg___closed__0));
v___f_193_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_193_, 0, v_toPure_191_);
v___f_194_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_194_, 0, v_toPure_191_);
lean_closure_set(v___f_194_, 1, v___f_192_);
lean_closure_set(v___f_194_, 2, v_inst_187_);
lean_closure_set(v___f_194_, 3, v_toBind_189_);
lean_closure_set(v___f_194_, 4, v_inst_185_);
lean_closure_set(v___f_194_, 5, v___f_193_);
v___x_195_ = lean_apply_4(v_toBind_189_, lean_box(0), lean_box(0), v_getTraceState_190_, v___f_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces(lean_object* v_m_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_printTraces___redArg(v_inst_197_, v_inst_198_, v_inst_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0(lean_object* v_x_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_unsigned_to_nat(32u);
v___x_203_ = lean_mk_empty_array_with_capacity(v___x_202_);
lean_dec_ref(v___x_203_);
v___x_204_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__2, &l_Lean_instInhabitedTraceState_default___closed__2_once, _init_l_Lean_instInhabitedTraceState_default___closed__2);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0___boxed(lean_object* v_x_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_resetTraceState___redArg___lam__0(v_x_205_);
lean_dec_ref(v_x_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg(lean_object* v_inst_208_){
_start:
{
lean_object* v_modifyTraceState_209_; lean_object* v___f_210_; lean_object* v___x_211_; 
v_modifyTraceState_209_ = lean_ctor_get(v_inst_208_, 0);
lean_inc(v_modifyTraceState_209_);
lean_dec_ref(v_inst_208_);
v___f_210_ = ((lean_object*)(l_Lean_resetTraceState___redArg___closed__0));
v___x_211_ = lean_apply_1(v_modifyTraceState_209_, v___f_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState(lean_object* v_m_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_resetTraceState___redArg(v_inst_213_);
return v___x_214_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(lean_object* v_a_215_, lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
uint8_t v___x_217_; 
v___x_217_ = 0;
return v___x_217_;
}
else
{
lean_object* v_key_218_; lean_object* v_tail_219_; uint8_t v___x_220_; 
v_key_218_ = lean_ctor_get(v_x_216_, 0);
v_tail_219_ = lean_ctor_get(v_x_216_, 2);
v___x_220_ = lean_name_eq(v_key_218_, v_a_215_);
if (v___x_220_ == 0)
{
v_x_216_ = v_tail_219_;
goto _start;
}
else
{
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_222_, lean_object* v_x_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_222_, v_x_223_);
lean_dec(v_x_223_);
lean_dec(v_a_222_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_226_; uint64_t v___x_227_; 
v___x_226_ = lean_unsigned_to_nat(1723u);
v___x_227_ = lean_uint64_of_nat(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(lean_object* v_m_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_buckets_230_; lean_object* v___x_231_; uint64_t v___y_233_; 
v_buckets_230_ = lean_ctor_get(v_m_228_, 1);
v___x_231_ = lean_array_get_size(v_buckets_230_);
if (lean_obj_tag(v_a_229_) == 0)
{
uint64_t v___x_247_; 
v___x_247_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_233_ = v___x_247_;
goto v___jp_232_;
}
else
{
uint64_t v_hash_248_; 
v_hash_248_ = lean_ctor_get_uint64(v_a_229_, sizeof(void*)*2);
v___y_233_ = v_hash_248_;
goto v___jp_232_;
}
v___jp_232_:
{
uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v_fold_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_234_ = 32ULL;
v___x_235_ = lean_uint64_shift_right(v___y_233_, v___x_234_);
v_fold_236_ = lean_uint64_xor(v___y_233_, v___x_235_);
v___x_237_ = 16ULL;
v___x_238_ = lean_uint64_shift_right(v_fold_236_, v___x_237_);
v___x_239_ = lean_uint64_xor(v_fold_236_, v___x_238_);
v___x_240_ = lean_uint64_to_usize(v___x_239_);
v___x_241_ = lean_usize_of_nat(v___x_231_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_sub(v___x_241_, v___x_242_);
v___x_244_ = lean_usize_land(v___x_240_, v___x_243_);
v___x_245_ = lean_array_uget_borrowed(v_buckets_230_, v___x_244_);
v___x_246_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_229_, v___x_245_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___boxed(lean_object* v_m_249_, lean_object* v_a_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_m_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object* v_inherited_253_, lean_object* v_opts_254_, lean_object* v_opt_255_){
_start:
{
lean_object* v_map_261_; lean_object* v___x_262_; 
v_map_261_ = lean_ctor_get(v_opts_254_, 0);
v___x_262_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_261_, v_opt_255_);
if (lean_obj_tag(v___x_262_) == 0)
{
goto v___jp_256_;
}
else
{
lean_object* v_val_263_; 
v_val_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_val_263_);
lean_dec_ref(v___x_262_);
if (lean_obj_tag(v_val_263_) == 1)
{
uint8_t v_v_264_; 
v_v_264_ = lean_ctor_get_uint8(v_val_263_, 0);
lean_dec_ref(v_val_263_);
return v_v_264_;
}
else
{
lean_dec(v_val_263_);
goto v___jp_256_;
}
}
v___jp_256_:
{
if (lean_obj_tag(v_opt_255_) == 1)
{
lean_object* v_pre_257_; uint8_t v___x_258_; 
v_pre_257_ = lean_ctor_get(v_opt_255_, 0);
v___x_258_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_inherited_253_, v_opt_255_);
if (v___x_258_ == 0)
{
return v___x_258_;
}
else
{
v_opt_255_ = v_pre_257_;
goto _start;
}
}
else
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go___boxed(lean_object* v_inherited_265_, lean_object* v_opts_266_, lean_object* v_opt_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_265_, v_opts_266_, v_opt_267_);
lean_dec(v_opt_267_);
lean_dec_ref(v_opts_266_);
lean_dec_ref(v_inherited_265_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(lean_object* v_00_u03b2_270_, lean_object* v_m_271_, lean_object* v_a_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_271_, v_a_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(lean_object* v_00_u03b2_274_, lean_object* v_m_275_, lean_object* v_a_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(v_00_u03b2_274_, v_m_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_m_275_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(lean_object* v_00_u03b2_279_, lean_object* v_a_280_, lean_object* v_x_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_280_, v_x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_283_, lean_object* v_a_284_, lean_object* v_x_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(v_00_u03b2_283_, v_a_284_, v_x_285_);
lean_dec(v_x_285_);
lean_dec(v_a_284_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT uint8_t l_Lean_checkTraceOption(lean_object* v_inherited_291_, lean_object* v_opts_292_, lean_object* v_cls_293_){
_start:
{
uint8_t v_hasTrace_294_; 
v_hasTrace_294_ = lean_ctor_get_uint8(v_opts_292_, sizeof(void*)*1);
if (v_hasTrace_294_ == 0)
{
lean_dec(v_cls_293_);
return v_hasTrace_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_296_ = l_Lean_Name_append(v___x_295_, v_cls_293_);
v___x_297_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_291_, v_opts_292_, v___x_296_);
lean_dec(v___x_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkTraceOption___boxed(lean_object* v_inherited_298_, lean_object* v_opts_299_, lean_object* v_cls_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Lean_checkTraceOption(v_inherited_298_, v_opts_299_, v_cls_300_);
lean_dec_ref(v_opts_299_);
lean_dec_ref(v_inherited_298_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0(lean_object* v_toPure_303_, lean_object* v_cls_304_, lean_object* v_____do__lift_305_, lean_object* v_____do__lift_306_){
_start:
{
uint8_t v_hasTrace_307_; 
v_hasTrace_307_ = lean_ctor_get_uint8(v_____do__lift_306_, sizeof(void*)*1);
if (v_hasTrace_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_cls_304_);
v___x_308_ = lean_box(v_hasTrace_307_);
v___x_309_ = lean_apply_2(v_toPure_303_, lean_box(0), v___x_308_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_310_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_311_ = l_Lean_Name_append(v___x_310_, v_cls_304_);
v___x_312_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_305_, v_____do__lift_306_, v___x_311_);
lean_dec(v___x_311_);
v___x_313_ = lean_box(v___x_312_);
v___x_314_ = lean_apply_2(v_toPure_303_, lean_box(0), v___x_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0___boxed(lean_object* v_toPure_315_, lean_object* v_cls_316_, lean_object* v_____do__lift_317_, lean_object* v_____do__lift_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_isTracingEnabledFor___redArg___lam__0(v_toPure_315_, v_cls_316_, v_____do__lift_317_, v_____do__lift_318_);
lean_dec_ref(v_____do__lift_318_);
lean_dec_ref(v_____do__lift_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__1(lean_object* v_toPure_320_, lean_object* v_cls_321_, lean_object* v_toBind_322_, lean_object* v_inst_323_, lean_object* v_____do__lift_324_){
_start:
{
lean_object* v___f_325_; lean_object* v___x_326_; 
v___f_325_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_325_, 0, v_toPure_320_);
lean_closure_set(v___f_325_, 1, v_cls_321_);
lean_closure_set(v___f_325_, 2, v_____do__lift_324_);
v___x_326_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v_inst_323_, v___f_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_cls_330_){
_start:
{
lean_object* v_toApplicative_331_; lean_object* v_toBind_332_; lean_object* v_getInheritedTraceOptions_333_; lean_object* v_toPure_334_; lean_object* v___f_335_; lean_object* v___x_336_; 
v_toApplicative_331_ = lean_ctor_get(v_inst_327_, 0);
lean_inc_ref(v_toApplicative_331_);
v_toBind_332_ = lean_ctor_get(v_inst_327_, 1);
lean_inc_n(v_toBind_332_, 2);
lean_dec_ref(v_inst_327_);
v_getInheritedTraceOptions_333_ = lean_ctor_get(v_inst_328_, 2);
lean_inc(v_getInheritedTraceOptions_333_);
lean_dec_ref(v_inst_328_);
v_toPure_334_ = lean_ctor_get(v_toApplicative_331_, 1);
lean_inc(v_toPure_334_);
lean_dec_ref(v_toApplicative_331_);
v___f_335_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_335_, 0, v_toPure_334_);
lean_closure_set(v___f_335_, 1, v_cls_330_);
lean_closure_set(v___f_335_, 2, v_toBind_332_);
lean_closure_set(v___f_335_, 3, v_inst_329_);
v___x_336_ = lean_apply_4(v_toBind_332_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_333_, v___f_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor(lean_object* v_m_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_cls_341_){
_start:
{
lean_object* v_toApplicative_342_; lean_object* v_toBind_343_; lean_object* v_getInheritedTraceOptions_344_; lean_object* v_toPure_345_; lean_object* v___f_346_; lean_object* v___x_347_; 
v_toApplicative_342_ = lean_ctor_get(v_inst_338_, 0);
lean_inc_ref(v_toApplicative_342_);
v_toBind_343_ = lean_ctor_get(v_inst_338_, 1);
lean_inc_n(v_toBind_343_, 2);
lean_dec_ref(v_inst_338_);
v_getInheritedTraceOptions_344_ = lean_ctor_get(v_inst_339_, 2);
lean_inc(v_getInheritedTraceOptions_344_);
lean_dec_ref(v_inst_339_);
v_toPure_345_ = lean_ctor_get(v_toApplicative_342_, 1);
lean_inc(v_toPure_345_);
lean_dec_ref(v_toApplicative_342_);
v___f_346_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_346_, 0, v_toPure_345_);
lean_closure_set(v___f_346_, 1, v_cls_341_);
lean_closure_set(v___f_346_, 2, v_toBind_343_);
lean_closure_set(v___f_346_, 3, v_inst_340_);
v___x_347_ = lean_apply_4(v_toBind_343_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_344_, v___f_346_);
return v___x_347_;
}
}
LEAN_EXPORT uint8_t lean_is_trace_class_enabled(lean_object* v_opts_348_, lean_object* v_cls_349_){
_start:
{
uint8_t v_hasTrace_351_; 
v_hasTrace_351_ = lean_ctor_get_uint8(v_opts_348_, sizeof(void*)*1);
if (v_hasTrace_351_ == 0)
{
lean_dec(v_cls_349_);
lean_dec_ref(v_opts_348_);
return v_hasTrace_351_;
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_352_ = l_Lean_inheritedTraceOptions;
v___x_353_ = lean_st_ref_get(v___x_352_);
v___x_354_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_355_ = l_Lean_Name_append(v___x_354_, v_cls_349_);
v___x_356_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_353_, v_opts_348_, v___x_355_);
lean_dec(v___x_355_);
lean_dec_ref(v_opts_348_);
lean_dec(v___x_353_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object* v_opts_357_, lean_object* v_cls_358_, lean_object* v_a_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = lean_is_trace_class_enabled(v_opts_357_, v_cls_358_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object* v_toPure_362_, lean_object* v_s_363_){
_start:
{
lean_object* v_traces_364_; lean_object* v___x_365_; 
v_traces_364_ = lean_ctor_get(v_s_363_, 0);
lean_inc_ref(v_traces_364_);
lean_dec_ref(v_s_363_);
v___x_365_ = lean_apply_2(v_toPure_362_, lean_box(0), v_traces_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object* v_inst_366_, lean_object* v_inst_367_){
_start:
{
lean_object* v_toApplicative_368_; lean_object* v_toBind_369_; lean_object* v_getTraceState_370_; lean_object* v_toPure_371_; lean_object* v___f_372_; lean_object* v___x_373_; 
v_toApplicative_368_ = lean_ctor_get(v_inst_366_, 0);
lean_inc_ref(v_toApplicative_368_);
v_toBind_369_ = lean_ctor_get(v_inst_366_, 1);
lean_inc(v_toBind_369_);
lean_dec_ref(v_inst_366_);
v_getTraceState_370_ = lean_ctor_get(v_inst_367_, 1);
lean_inc(v_getTraceState_370_);
lean_dec_ref(v_inst_367_);
v_toPure_371_ = lean_ctor_get(v_toApplicative_368_, 1);
lean_inc(v_toPure_371_);
lean_dec_ref(v_toApplicative_368_);
v___f_372_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_372_, 0, v_toPure_371_);
v___x_373_ = lean_apply_4(v_toBind_369_, lean_box(0), lean_box(0), v_getTraceState_370_, v___f_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object* v_m_374_, lean_object* v_inst_375_, lean_object* v_inst_376_){
_start:
{
lean_object* v_toApplicative_377_; lean_object* v_toBind_378_; lean_object* v_getTraceState_379_; lean_object* v_toPure_380_; lean_object* v___f_381_; lean_object* v___x_382_; 
v_toApplicative_377_ = lean_ctor_get(v_inst_375_, 0);
lean_inc_ref(v_toApplicative_377_);
v_toBind_378_ = lean_ctor_get(v_inst_375_, 1);
lean_inc(v_toBind_378_);
lean_dec_ref(v_inst_375_);
v_getTraceState_379_ = lean_ctor_get(v_inst_376_, 1);
lean_inc(v_getTraceState_379_);
lean_dec_ref(v_inst_376_);
v_toPure_380_ = lean_ctor_get(v_toApplicative_377_, 1);
lean_inc(v_toPure_380_);
lean_dec_ref(v_toApplicative_377_);
v___f_381_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_381_, 0, v_toPure_380_);
v___x_382_ = lean_apply_4(v_toBind_378_, lean_box(0), lean_box(0), v_getTraceState_379_, v___f_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object* v_f_383_, lean_object* v_s_384_){
_start:
{
uint64_t v_tid_385_; lean_object* v_traces_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_394_; 
v_tid_385_ = lean_ctor_get_uint64(v_s_384_, sizeof(void*)*1);
v_traces_386_ = lean_ctor_get(v_s_384_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v_s_384_);
if (v_isSharedCheck_394_ == 0)
{
v___x_388_ = v_s_384_;
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_traces_386_);
lean_dec(v_s_384_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = lean_apply_1(v_f_383_, v_traces_386_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_390_);
v___x_392_ = v___x_388_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
lean_ctor_set_uint64(v_reuseFailAlloc_393_, sizeof(void*)*1, v_tid_385_);
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
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object* v_inst_395_, lean_object* v_f_396_){
_start:
{
lean_object* v_modifyTraceState_397_; lean_object* v___f_398_; lean_object* v___x_399_; 
v_modifyTraceState_397_ = lean_ctor_get(v_inst_395_, 0);
lean_inc(v_modifyTraceState_397_);
lean_dec_ref(v_inst_395_);
v___f_398_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_398_, 0, v_f_396_);
v___x_399_ = lean_apply_1(v_modifyTraceState_397_, v___f_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object* v_m_400_, lean_object* v_inst_401_, lean_object* v_f_402_){
_start:
{
lean_object* v_modifyTraceState_403_; lean_object* v___f_404_; lean_object* v___x_405_; 
v_modifyTraceState_403_ = lean_ctor_get(v_inst_401_, 0);
lean_inc(v_modifyTraceState_403_);
lean_dec_ref(v_inst_401_);
v___f_404_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_404_, 0, v_f_402_);
v___x_405_ = lean_apply_1(v_modifyTraceState_403_, v___f_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object* v_s_406_, lean_object* v_x_407_){
_start:
{
lean_inc_ref(v_s_406_);
return v_s_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object* v_s_408_, lean_object* v_x_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_setTraceState___redArg___lam__0(v_s_408_, v_x_409_);
lean_dec_ref(v_x_409_);
lean_dec_ref(v_s_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object* v_inst_411_, lean_object* v_s_412_){
_start:
{
lean_object* v_modifyTraceState_413_; lean_object* v___f_414_; lean_object* v___x_415_; 
v_modifyTraceState_413_ = lean_ctor_get(v_inst_411_, 0);
lean_inc(v_modifyTraceState_413_);
lean_dec_ref(v_inst_411_);
v___f_414_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_414_, 0, v_s_412_);
v___x_415_ = lean_apply_1(v_modifyTraceState_413_, v___f_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object* v_m_416_, lean_object* v_inst_417_, lean_object* v_s_418_){
_start:
{
lean_object* v_modifyTraceState_419_; lean_object* v___f_420_; lean_object* v___x_421_; 
v_modifyTraceState_419_ = lean_ctor_get(v_inst_417_, 0);
lean_inc(v_modifyTraceState_419_);
lean_dec_ref(v_inst_417_);
v___f_420_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_420_, 0, v_s_418_);
v___x_421_ = lean_apply_1(v_modifyTraceState_419_, v___f_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object* v_s_422_){
_start:
{
uint64_t v_tid_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_433_; 
v_tid_423_ = lean_ctor_get_uint64(v_s_422_, sizeof(void*)*1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_s_422_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v_s_422_, 0);
lean_dec(v_unused_434_);
v___x_425_ = v_s_422_;
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
else
{
lean_dec(v_s_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_427_ = lean_unsigned_to_nat(32u);
v___x_428_ = lean_mk_empty_array_with_capacity(v___x_427_);
lean_dec_ref(v___x_428_);
v___x_429_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__1, &l_Lean_instInhabitedTraceState_default___closed__1_once, _init_l_Lean_instInhabitedTraceState_default___closed__1);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_429_);
v___x_431_ = v___x_425_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
lean_ctor_set_uint64(v_reuseFailAlloc_432_, sizeof(void*)*1, v_tid_423_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object* v_toPure_435_, lean_object* v_oldTraces_436_, lean_object* v_____r_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = lean_apply_2(v_toPure_435_, lean_box(0), v_oldTraces_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object* v_toPure_439_, lean_object* v_modifyTraceState_440_, lean_object* v___f_441_, lean_object* v_toBind_442_, lean_object* v_oldTraces_443_){
_start:
{
lean_object* v___f_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___f_444_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_444_, 0, v_toPure_439_);
lean_closure_set(v___f_444_, 1, v_oldTraces_443_);
v___x_445_ = lean_apply_1(v_modifyTraceState_440_, v___f_441_);
v___x_446_ = lean_apply_4(v_toBind_442_, lean_box(0), lean_box(0), v___x_445_, v___f_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object* v_inst_448_, lean_object* v_inst_449_){
_start:
{
lean_object* v_toApplicative_450_; lean_object* v_toBind_451_; lean_object* v_modifyTraceState_452_; lean_object* v_getTraceState_453_; lean_object* v_toPure_454_; lean_object* v___f_455_; lean_object* v___f_456_; lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_toApplicative_450_ = lean_ctor_get(v_inst_448_, 0);
lean_inc_ref(v_toApplicative_450_);
v_toBind_451_ = lean_ctor_get(v_inst_448_, 1);
lean_inc_n(v_toBind_451_, 3);
lean_dec_ref(v_inst_448_);
v_modifyTraceState_452_ = lean_ctor_get(v_inst_449_, 0);
lean_inc(v_modifyTraceState_452_);
v_getTraceState_453_ = lean_ctor_get(v_inst_449_, 1);
lean_inc(v_getTraceState_453_);
lean_dec_ref(v_inst_449_);
v_toPure_454_ = lean_ctor_get(v_toApplicative_450_, 1);
lean_inc_n(v_toPure_454_, 2);
lean_dec_ref(v_toApplicative_450_);
v___f_455_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0));
v___f_456_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_456_, 0, v_toPure_454_);
lean_closure_set(v___f_456_, 1, v_modifyTraceState_452_);
lean_closure_set(v___f_456_, 2, v___f_455_);
lean_closure_set(v___f_456_, 3, v_toBind_451_);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_457_, 0, v_toPure_454_);
v___x_458_ = lean_apply_4(v_toBind_451_, lean_box(0), lean_box(0), v_getTraceState_453_, v___f_457_);
v___x_459_ = lean_apply_4(v_toBind_451_, lean_box(0), lean_box(0), v___x_458_, v___f_456_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object* v_m_460_, lean_object* v_inst_461_, lean_object* v_inst_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_461_, v_inst_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object* v_ref_464_, lean_object* v_msg_465_, lean_object* v_s_466_){
_start:
{
uint64_t v_tid_467_; lean_object* v_traces_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_477_; 
v_tid_467_ = lean_ctor_get_uint64(v_s_466_, sizeof(void*)*1);
v_traces_468_ = lean_ctor_get(v_s_466_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_s_466_);
if (v_isSharedCheck_477_ == 0)
{
v___x_470_ = v_s_466_;
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_traces_468_);
lean_dec(v_s_466_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v_ref_464_);
lean_ctor_set(v___x_472_, 1, v_msg_465_);
v___x_473_ = l_Lean_PersistentArray_push___redArg(v_traces_468_, v___x_472_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_473_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
lean_ctor_set_uint64(v_reuseFailAlloc_476_, sizeof(void*)*1, v_tid_467_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object* v_inst_478_, lean_object* v_ref_479_, lean_object* v_msg_480_){
_start:
{
lean_object* v_modifyTraceState_481_; lean_object* v___f_482_; lean_object* v___x_483_; 
v_modifyTraceState_481_ = lean_ctor_get(v_inst_478_, 0);
lean_inc(v_modifyTraceState_481_);
lean_dec_ref(v_inst_478_);
v___f_482_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__0), 3, 2);
lean_closure_set(v___f_482_, 0, v_ref_479_);
lean_closure_set(v___f_482_, 1, v_msg_480_);
v___x_483_ = lean_apply_1(v_modifyTraceState_481_, v___f_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_msg_486_, lean_object* v_toBind_487_, lean_object* v_ref_488_){
_start:
{
lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___f_489_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__1), 3, 2);
lean_closure_set(v___f_489_, 0, v_inst_484_);
lean_closure_set(v___f_489_, 1, v_ref_488_);
v___x_490_ = lean_apply_1(v_inst_485_, v_msg_486_);
v___x_491_ = lean_apply_4(v_toBind_487_, lean_box(0), lean_box(0), v___x_490_, v___f_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_msg_496_){
_start:
{
lean_object* v_toBind_497_; lean_object* v_getRef_498_; lean_object* v___f_499_; lean_object* v___x_500_; 
v_toBind_497_ = lean_ctor_get(v_inst_492_, 1);
lean_inc_n(v_toBind_497_, 2);
lean_dec_ref(v_inst_492_);
v_getRef_498_ = lean_ctor_get(v_inst_494_, 0);
lean_inc(v_getRef_498_);
lean_dec_ref(v_inst_494_);
v___f_499_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__2), 5, 4);
lean_closure_set(v___f_499_, 0, v_inst_493_);
lean_closure_set(v___f_499_, 1, v_inst_495_);
lean_closure_set(v___f_499_, 2, v_msg_496_);
lean_closure_set(v___f_499_, 3, v_toBind_497_);
v___x_500_ = lean_apply_4(v_toBind_497_, lean_box(0), lean_box(0), v_getRef_498_, v___f_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object* v_m_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_msg_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_addRawTrace___redArg(v_inst_502_, v_inst_503_, v_inst_504_, v_inst_505_, v_msg_506_);
return v___x_507_;
}
}
static double _init_l_Lean_addTrace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_508_; double v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_float_of_nat(v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object* v_cls_513_, lean_object* v_msg_514_, lean_object* v_ref_515_, lean_object* v_s_516_){
_start:
{
uint64_t v_tid_517_; lean_object* v_traces_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_534_; 
v_tid_517_ = lean_ctor_get_uint64(v_s_516_, sizeof(void*)*1);
v_traces_518_ = lean_ctor_get(v_s_516_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_s_516_);
if (v_isSharedCheck_534_ == 0)
{
v___x_520_ = v_s_516_;
v_isShared_521_ = v_isSharedCheck_534_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_traces_518_);
lean_dec(v_s_516_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_534_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; double v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_522_ = lean_box(0);
v___x_523_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
v___x_524_ = 0;
v___x_525_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_526_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_526_, 0, v_cls_513_);
lean_ctor_set(v___x_526_, 1, v___x_522_);
lean_ctor_set(v___x_526_, 2, v___x_525_);
lean_ctor_set_float(v___x_526_, sizeof(void*)*3, v___x_523_);
lean_ctor_set_float(v___x_526_, sizeof(void*)*3 + 8, v___x_523_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*3 + 16, v___x_524_);
v___x_527_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
v___x_528_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v_msg_514_);
lean_ctor_set(v___x_528_, 2, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_ref_515_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_PersistentArray_push___redArg(v_traces_518_, v___x_529_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_530_);
v___x_532_ = v___x_520_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
lean_ctor_set_uint64(v_reuseFailAlloc_533_, sizeof(void*)*1, v_tid_517_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object* v_inst_535_, lean_object* v_cls_536_, lean_object* v_ref_537_, lean_object* v_msg_538_){
_start:
{
lean_object* v_modifyTraceState_539_; lean_object* v___f_540_; lean_object* v___x_541_; 
v_modifyTraceState_539_ = lean_ctor_get(v_inst_535_, 0);
lean_inc(v_modifyTraceState_539_);
lean_dec_ref(v_inst_535_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_540_, 0, v_cls_536_);
lean_closure_set(v___f_540_, 1, v_msg_538_);
lean_closure_set(v___f_540_, 2, v_ref_537_);
v___x_541_ = lean_apply_1(v_modifyTraceState_539_, v___f_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object* v_inst_542_, lean_object* v_cls_543_, lean_object* v_inst_544_, lean_object* v_msg_545_, lean_object* v_toBind_546_, lean_object* v_ref_547_){
_start:
{
lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___f_548_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__1), 4, 3);
lean_closure_set(v___f_548_, 0, v_inst_542_);
lean_closure_set(v___f_548_, 1, v_cls_543_);
lean_closure_set(v___f_548_, 2, v_ref_547_);
v___x_549_ = lean_apply_1(v_inst_544_, v_msg_545_);
v___x_550_ = lean_apply_4(v_toBind_546_, lean_box(0), lean_box(0), v___x_549_, v___f_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_cls_555_, lean_object* v_msg_556_){
_start:
{
lean_object* v_toBind_557_; lean_object* v_getRef_558_; lean_object* v___f_559_; lean_object* v___x_560_; 
v_toBind_557_ = lean_ctor_get(v_inst_551_, 1);
lean_inc_n(v_toBind_557_, 2);
lean_dec_ref(v_inst_551_);
v_getRef_558_ = lean_ctor_get(v_inst_553_, 0);
lean_inc(v_getRef_558_);
lean_dec_ref(v_inst_553_);
v___f_559_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__2), 6, 5);
lean_closure_set(v___f_559_, 0, v_inst_552_);
lean_closure_set(v___f_559_, 1, v_cls_555_);
lean_closure_set(v___f_559_, 2, v_inst_554_);
lean_closure_set(v___f_559_, 3, v_msg_556_);
lean_closure_set(v___f_559_, 4, v_toBind_557_);
v___x_560_ = lean_apply_4(v_toBind_557_, lean_box(0), lean_box(0), v_getRef_558_, v___f_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object* v_m_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_cls_566_, lean_object* v_msg_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_addTrace___redArg(v_inst_562_, v_inst_563_, v_inst_564_, v_inst_565_, v_cls_566_, v_msg_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0(lean_object* v_toPure_569_, lean_object* v_msg_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_cls_575_, uint8_t v_____do__lift_576_){
_start:
{
if (v_____do__lift_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v_cls_575_);
lean_dec(v_inst_574_);
lean_dec_ref(v_inst_573_);
lean_dec_ref(v_inst_572_);
lean_dec_ref(v_inst_571_);
lean_dec_ref(v_msg_570_);
v___x_577_ = lean_box(0);
v___x_578_ = lean_apply_2(v_toPure_569_, lean_box(0), v___x_577_);
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_toPure_569_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_apply_1(v_msg_570_, v___x_579_);
v___x_581_ = l_Lean_addTrace___redArg(v_inst_571_, v_inst_572_, v_inst_573_, v_inst_574_, v_cls_575_, v___x_580_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object* v_toPure_582_, lean_object* v_msg_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_cls_588_, lean_object* v_____do__lift_589_){
_start:
{
uint8_t v_____do__lift_148__boxed_590_; lean_object* v_res_591_; 
v_____do__lift_148__boxed_590_ = lean_unbox(v_____do__lift_589_);
v_res_591_ = l_Lean_trace___redArg___lam__0(v_toPure_582_, v_msg_583_, v_inst_584_, v_inst_585_, v_inst_586_, v_inst_587_, v_cls_588_, v_____do__lift_148__boxed_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_cls_597_, lean_object* v_msg_598_){
_start:
{
lean_object* v_toApplicative_599_; lean_object* v_toBind_600_; lean_object* v_getInheritedTraceOptions_601_; lean_object* v_toPure_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_toApplicative_599_ = lean_ctor_get(v_inst_592_, 0);
v_toBind_600_ = lean_ctor_get(v_inst_592_, 1);
lean_inc_n(v_toBind_600_, 3);
v_getInheritedTraceOptions_601_ = lean_ctor_get(v_inst_593_, 2);
lean_inc(v_getInheritedTraceOptions_601_);
v_toPure_602_ = lean_ctor_get(v_toApplicative_599_, 1);
lean_inc_n(v_toPure_602_, 2);
lean_inc(v_cls_597_);
v___f_603_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_603_, 0, v_toPure_602_);
lean_closure_set(v___f_603_, 1, v_msg_598_);
lean_closure_set(v___f_603_, 2, v_inst_592_);
lean_closure_set(v___f_603_, 3, v_inst_593_);
lean_closure_set(v___f_603_, 4, v_inst_594_);
lean_closure_set(v___f_603_, 5, v_inst_595_);
lean_closure_set(v___f_603_, 6, v_cls_597_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_604_, 0, v_toPure_602_);
lean_closure_set(v___f_604_, 1, v_cls_597_);
lean_closure_set(v___f_604_, 2, v_toBind_600_);
lean_closure_set(v___f_604_, 3, v_inst_596_);
v___x_605_ = lean_apply_4(v_toBind_600_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_601_, v___f_604_);
v___x_606_ = lean_apply_4(v_toBind_600_, lean_box(0), lean_box(0), v___x_605_, v___f_603_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace(lean_object* v_m_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_cls_613_, lean_object* v_msg_614_){
_start:
{
lean_object* v_toApplicative_615_; lean_object* v_toBind_616_; lean_object* v_getInheritedTraceOptions_617_; lean_object* v_toPure_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_toApplicative_615_ = lean_ctor_get(v_inst_608_, 0);
v_toBind_616_ = lean_ctor_get(v_inst_608_, 1);
lean_inc_n(v_toBind_616_, 3);
v_getInheritedTraceOptions_617_ = lean_ctor_get(v_inst_609_, 2);
lean_inc(v_getInheritedTraceOptions_617_);
v_toPure_618_ = lean_ctor_get(v_toApplicative_615_, 1);
lean_inc_n(v_toPure_618_, 2);
lean_inc(v_cls_613_);
v___f_619_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_619_, 0, v_toPure_618_);
lean_closure_set(v___f_619_, 1, v_msg_614_);
lean_closure_set(v___f_619_, 2, v_inst_608_);
lean_closure_set(v___f_619_, 3, v_inst_609_);
lean_closure_set(v___f_619_, 4, v_inst_610_);
lean_closure_set(v___f_619_, 5, v_inst_611_);
lean_closure_set(v___f_619_, 6, v_cls_613_);
v___f_620_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_620_, 0, v_toPure_618_);
lean_closure_set(v___f_620_, 1, v_cls_613_);
lean_closure_set(v___f_620_, 2, v_toBind_616_);
lean_closure_set(v___f_620_, 3, v_inst_612_);
v___x_621_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_617_, v___f_620_);
v___x_622_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_621_, v___f_619_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_cls_627_, lean_object* v_msg_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_addTrace___redArg(v_inst_623_, v_inst_624_, v_inst_625_, v_inst_626_, v_cls_627_, v_msg_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1(lean_object* v_toPure_630_, lean_object* v_toBind_631_, lean_object* v_mkMsg_632_, lean_object* v___f_633_, uint8_t v_____do__lift_634_){
_start:
{
if (v_____do__lift_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v___f_633_);
lean_dec(v_mkMsg_632_);
lean_dec(v_toBind_631_);
v___x_635_ = lean_box(0);
v___x_636_ = lean_apply_2(v_toPure_630_, lean_box(0), v___x_635_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; 
lean_dec(v_toPure_630_);
v___x_637_ = lean_apply_4(v_toBind_631_, lean_box(0), lean_box(0), v_mkMsg_632_, v___f_633_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object* v_toPure_638_, lean_object* v_toBind_639_, lean_object* v_mkMsg_640_, lean_object* v___f_641_, lean_object* v_____do__lift_642_){
_start:
{
uint8_t v_____do__lift_154__boxed_643_; lean_object* v_res_644_; 
v_____do__lift_154__boxed_643_ = lean_unbox(v_____do__lift_642_);
v_res_644_ = l_Lean_traceM___redArg___lam__1(v_toPure_638_, v_toBind_639_, v_mkMsg_640_, v___f_641_, v_____do__lift_154__boxed_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_cls_650_, lean_object* v_mkMsg_651_){
_start:
{
lean_object* v_toApplicative_652_; lean_object* v_toBind_653_; lean_object* v_getInheritedTraceOptions_654_; lean_object* v_toPure_655_; lean_object* v___f_656_; lean_object* v___f_657_; lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_toApplicative_652_ = lean_ctor_get(v_inst_645_, 0);
v_toBind_653_ = lean_ctor_get(v_inst_645_, 1);
lean_inc_n(v_toBind_653_, 4);
v_getInheritedTraceOptions_654_ = lean_ctor_get(v_inst_646_, 2);
lean_inc(v_getInheritedTraceOptions_654_);
v_toPure_655_ = lean_ctor_get(v_toApplicative_652_, 1);
lean_inc_n(v_toPure_655_, 2);
lean_inc(v_cls_650_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_656_, 0, v_inst_645_);
lean_closure_set(v___f_656_, 1, v_inst_646_);
lean_closure_set(v___f_656_, 2, v_inst_647_);
lean_closure_set(v___f_656_, 3, v_inst_648_);
lean_closure_set(v___f_656_, 4, v_cls_650_);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_657_, 0, v_toPure_655_);
lean_closure_set(v___f_657_, 1, v_toBind_653_);
lean_closure_set(v___f_657_, 2, v_mkMsg_651_);
lean_closure_set(v___f_657_, 3, v___f_656_);
v___f_658_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_658_, 0, v_toPure_655_);
lean_closure_set(v___f_658_, 1, v_cls_650_);
lean_closure_set(v___f_658_, 2, v_toBind_653_);
lean_closure_set(v___f_658_, 3, v_inst_649_);
v___x_659_ = lean_apply_4(v_toBind_653_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_654_, v___f_658_);
v___x_660_ = lean_apply_4(v_toBind_653_, lean_box(0), lean_box(0), v___x_659_, v___f_657_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object* v_m_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_cls_667_, lean_object* v_mkMsg_668_){
_start:
{
lean_object* v_toApplicative_669_; lean_object* v_toBind_670_; lean_object* v_getInheritedTraceOptions_671_; lean_object* v_toPure_672_; lean_object* v___f_673_; lean_object* v___f_674_; lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_toApplicative_669_ = lean_ctor_get(v_inst_662_, 0);
v_toBind_670_ = lean_ctor_get(v_inst_662_, 1);
lean_inc_n(v_toBind_670_, 4);
v_getInheritedTraceOptions_671_ = lean_ctor_get(v_inst_663_, 2);
lean_inc(v_getInheritedTraceOptions_671_);
v_toPure_672_ = lean_ctor_get(v_toApplicative_669_, 1);
lean_inc_n(v_toPure_672_, 2);
lean_inc(v_cls_667_);
v___f_673_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_673_, 0, v_inst_662_);
lean_closure_set(v___f_673_, 1, v_inst_663_);
lean_closure_set(v___f_673_, 2, v_inst_664_);
lean_closure_set(v___f_673_, 3, v_inst_665_);
lean_closure_set(v___f_673_, 4, v_cls_667_);
v___f_674_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_674_, 0, v_toPure_672_);
lean_closure_set(v___f_674_, 1, v_toBind_670_);
lean_closure_set(v___f_674_, 2, v_mkMsg_668_);
lean_closure_set(v___f_674_, 3, v___f_673_);
v___f_675_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_675_, 0, v_toPure_672_);
lean_closure_set(v___f_675_, 1, v_cls_667_);
lean_closure_set(v___f_675_, 2, v_toBind_670_);
lean_closure_set(v___f_675_, 3, v_inst_666_);
v___x_676_ = lean_apply_4(v_toBind_670_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_671_, v___f_675_);
v___x_677_ = lean_apply_4(v_toBind_670_, lean_box(0), lean_box(0), v___x_676_, v___f_674_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object* v_x_678_){
_start:
{
lean_object* v_msg_679_; 
v_msg_679_ = lean_ctor_get(v_x_678_, 1);
lean_inc_ref(v_msg_679_);
return v_msg_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object* v_x_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_680_);
lean_dec_ref(v_x_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object* v_ref_682_, lean_object* v_msg_683_, lean_object* v_oldTraces_684_, lean_object* v_s_685_){
_start:
{
uint64_t v_tid_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v_tid_686_ = lean_ctor_get_uint64(v_s_685_, sizeof(void*)*1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_s_685_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_s_685_, 0);
lean_dec(v_unused_696_);
v___x_688_ = v_s_685_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_dec(v_s_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_ref_682_);
lean_ctor_set(v___x_690_, 1, v_msg_683_);
v___x_691_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_684_, v___x_690_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
lean_ctor_set_uint64(v_reuseFailAlloc_694_, sizeof(void*)*1, v_tid_686_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object* v_ref_697_, lean_object* v_oldTraces_698_, lean_object* v_modifyTraceState_699_, lean_object* v_msg_700_){
_start:
{
lean_object* v___f_701_; lean_object* v___x_702_; 
v___f_701_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0), 4, 3);
lean_closure_set(v___f_701_, 0, v_ref_697_);
lean_closure_set(v___f_701_, 1, v_msg_700_);
lean_closure_set(v___f_701_, 2, v_oldTraces_698_);
v___x_702_ = lean_apply_1(v_modifyTraceState_699_, v___f_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object* v___f_722_, lean_object* v_data_723_, lean_object* v_msg_724_, lean_object* v_inst_725_, lean_object* v_toBind_726_, lean_object* v___f_727_, lean_object* v_____do__lift_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; size_t v_sz_731_; size_t v___x_732_; lean_object* v___x_733_; lean_object* v_msg_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_729_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_728_);
v___x_730_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v_sz_731_ = lean_array_size(v___x_729_);
v___x_732_ = ((size_t)0ULL);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_730_, v___f_722_, v_sz_731_, v___x_732_, v___x_729_);
v_msg_734_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_734_, 0, v_data_723_);
lean_ctor_set(v_msg_734_, 1, v_msg_724_);
lean_ctor_set(v_msg_734_, 2, v___x_733_);
v___x_735_ = lean_apply_1(v_inst_725_, v_msg_734_);
v___x_736_ = lean_apply_4(v_toBind_726_, lean_box(0), lean_box(0), v___x_735_, v___f_727_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object* v___f_737_, lean_object* v_data_738_, lean_object* v_msg_739_, lean_object* v_inst_740_, lean_object* v_toBind_741_, lean_object* v___f_742_, lean_object* v_____do__lift_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(v___f_737_, v_data_738_, v_msg_739_, v_inst_740_, v_toBind_741_, v___f_742_, v_____do__lift_743_);
lean_dec_ref(v_____do__lift_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object* v_ref_745_, lean_object* v_withRef_746_, lean_object* v___x_747_, lean_object* v_oldRef_748_){
_start:
{
lean_object* v_ref_749_; lean_object* v___x_750_; 
v_ref_749_ = l_Lean_replaceRef(v_ref_745_, v_oldRef_748_);
v___x_750_ = lean_apply_3(v_withRef_746_, lean_box(0), v_ref_749_, v___x_747_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object* v_ref_751_, lean_object* v_withRef_752_, lean_object* v___x_753_, lean_object* v_oldRef_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(v_ref_751_, v_withRef_752_, v___x_753_, v_oldRef_754_);
lean_dec(v_oldRef_754_);
lean_dec(v_ref_751_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_oldTraces_761_, lean_object* v_data_762_, lean_object* v_ref_763_, lean_object* v_msg_764_){
_start:
{
lean_object* v_toApplicative_765_; lean_object* v_toBind_766_; lean_object* v_modifyTraceState_767_; lean_object* v_getTraceState_768_; lean_object* v_toPure_769_; lean_object* v_getRef_770_; lean_object* v_withRef_771_; lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v___x_779_; 
v_toApplicative_765_ = lean_ctor_get(v_inst_757_, 0);
lean_inc_ref(v_toApplicative_765_);
v_toBind_766_ = lean_ctor_get(v_inst_757_, 1);
lean_inc_n(v_toBind_766_, 4);
lean_dec_ref(v_inst_757_);
v_modifyTraceState_767_ = lean_ctor_get(v_inst_758_, 0);
lean_inc(v_modifyTraceState_767_);
v_getTraceState_768_ = lean_ctor_get(v_inst_758_, 1);
lean_inc(v_getTraceState_768_);
lean_dec_ref(v_inst_758_);
v_toPure_769_ = lean_ctor_get(v_toApplicative_765_, 1);
lean_inc(v_toPure_769_);
lean_dec_ref(v_toApplicative_765_);
v_getRef_770_ = lean_ctor_get(v_inst_759_, 0);
lean_inc(v_getRef_770_);
v_withRef_771_ = lean_ctor_get(v_inst_759_, 1);
lean_inc(v_withRef_771_);
lean_dec_ref(v_inst_759_);
v___f_772_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_772_, 0, v_toPure_769_);
v___x_773_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v_getTraceState_768_, v___f_772_);
v___f_774_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0));
lean_inc(v_ref_763_);
v___f_775_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2), 4, 3);
lean_closure_set(v___f_775_, 0, v_ref_763_);
lean_closure_set(v___f_775_, 1, v_oldTraces_761_);
lean_closure_set(v___f_775_, 2, v_modifyTraceState_767_);
v___f_776_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_776_, 0, v___f_774_);
lean_closure_set(v___f_776_, 1, v_data_762_);
lean_closure_set(v___f_776_, 2, v_msg_764_);
lean_closure_set(v___f_776_, 3, v_inst_760_);
lean_closure_set(v___f_776_, 4, v_toBind_766_);
lean_closure_set(v___f_776_, 5, v___f_775_);
v___x_777_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v___x_773_, v___f_776_);
v___f_778_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_778_, 0, v_ref_763_);
lean_closure_set(v___f_778_, 1, v_withRef_771_);
lean_closure_set(v___f_778_, 2, v___x_777_);
v___x_779_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v_getRef_770_, v___f_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object* v_m_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_oldTraces_785_, lean_object* v_data_786_, lean_object* v_ref_787_, lean_object* v_msg_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_781_, v_inst_782_, v_inst_783_, v_inst_784_, v_oldTraces_785_, v_data_786_, v_ref_787_, v_msg_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object* v_name_790_, lean_object* v_decl_791_, lean_object* v_ref_792_){
_start:
{
lean_object* v_defValue_794_; lean_object* v_descr_795_; lean_object* v_deprecation_x3f_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_defValue_794_ = lean_ctor_get(v_decl_791_, 0);
v_descr_795_ = lean_ctor_get(v_decl_791_, 1);
v_deprecation_x3f_796_ = lean_ctor_get(v_decl_791_, 2);
v___x_797_ = lean_alloc_ctor(1, 0, 1);
v___x_798_ = lean_unbox(v_defValue_794_);
lean_ctor_set_uint8(v___x_797_, 0, v___x_798_);
lean_inc(v_deprecation_x3f_796_);
lean_inc_ref(v_descr_795_);
lean_inc_n(v_name_790_, 2);
v___x_799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_799_, 0, v_name_790_);
lean_ctor_set(v___x_799_, 1, v_ref_792_);
lean_ctor_set(v___x_799_, 2, v___x_797_);
lean_ctor_set(v___x_799_, 3, v_descr_795_);
lean_ctor_set(v___x_799_, 4, v_deprecation_x3f_796_);
v___x_800_ = lean_register_option(v_name_790_, v___x_799_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___x_800_, 0);
lean_dec(v_unused_809_);
v___x_802_ = v___x_800_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_dec(v___x_800_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_inc(v_defValue_794_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_name_790_);
lean_ctor_set(v___x_804_, 1, v_defValue_794_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_804_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_name_790_);
v_a_810_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_800_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_800_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_818_, lean_object* v_decl_819_, lean_object* v_ref_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_818_, v_decl_819_, v_ref_820_);
lean_dec_ref(v_decl_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_838_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_839_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_840_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_841_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_838_, v___x_839_, v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object* v_name_844_, lean_object* v_decl_845_, lean_object* v_ref_846_){
_start:
{
lean_object* v_defValue_848_; lean_object* v_descr_849_; lean_object* v_deprecation_x3f_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_defValue_848_ = lean_ctor_get(v_decl_845_, 0);
v_descr_849_ = lean_ctor_get(v_decl_845_, 1);
v_deprecation_x3f_850_ = lean_ctor_get(v_decl_845_, 2);
lean_inc(v_defValue_848_);
v___x_851_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_851_, 0, v_defValue_848_);
lean_inc(v_deprecation_x3f_850_);
lean_inc_ref(v_descr_849_);
lean_inc_n(v_name_844_, 2);
v___x_852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_852_, 0, v_name_844_);
lean_ctor_set(v___x_852_, 1, v_ref_846_);
lean_ctor_set(v___x_852_, 2, v___x_851_);
lean_ctor_set(v___x_852_, 3, v_descr_849_);
lean_ctor_set(v___x_852_, 4, v_deprecation_x3f_850_);
v___x_853_ = lean_register_option(v_name_844_, v___x_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_861_; 
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v___x_853_, 0);
lean_dec(v_unused_862_);
v___x_855_ = v___x_853_;
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
else
{
lean_dec(v___x_853_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
lean_inc(v_defValue_848_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_name_844_);
lean_ctor_set(v___x_857_, 1, v_defValue_848_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec(v_name_844_);
v_a_863_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_853_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_853_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_871_, lean_object* v_decl_872_, lean_object* v_ref_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_871_, v_decl_872_, v_ref_873_);
lean_dec_ref(v_decl_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_892_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_893_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_894_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_895_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_892_, v___x_893_, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_915_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_916_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_917_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_918_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_915_, v___x_916_, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object* v_name_921_, lean_object* v_decl_922_, lean_object* v_ref_923_){
_start:
{
lean_object* v_defValue_925_; lean_object* v_descr_926_; lean_object* v_deprecation_x3f_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_defValue_925_ = lean_ctor_get(v_decl_922_, 0);
v_descr_926_ = lean_ctor_get(v_decl_922_, 1);
v_deprecation_x3f_927_ = lean_ctor_get(v_decl_922_, 2);
lean_inc(v_defValue_925_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v_defValue_925_);
lean_inc(v_deprecation_x3f_927_);
lean_inc_ref(v_descr_926_);
lean_inc_n(v_name_921_, 2);
v___x_929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_929_, 0, v_name_921_);
lean_ctor_set(v___x_929_, 1, v_ref_923_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
lean_ctor_set(v___x_929_, 3, v_descr_926_);
lean_ctor_set(v___x_929_, 4, v_deprecation_x3f_927_);
v___x_930_ = lean_register_option(v_name_921_, v___x_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_938_; 
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v___x_930_, 0);
lean_dec(v_unused_939_);
v___x_932_ = v___x_930_;
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
else
{
lean_dec(v___x_930_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
lean_inc(v_defValue_925_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_name_921_);
lean_ctor_set(v___x_934_, 1, v_defValue_925_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_934_);
v___x_936_ = v___x_932_;
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
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_name_921_);
v_a_940_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_930_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_930_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_948_, lean_object* v_decl_949_, lean_object* v_ref_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_948_, v_decl_949_, v_ref_950_);
lean_dec_ref(v_decl_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_970_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_971_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_972_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_969_, v___x_970_, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_992_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_993_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_994_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_995_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_992_, v___x_993_, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4____boxed(lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
return v_res_997_;
}
}
LEAN_EXPORT uint8_t l_Lean_trace_profiler_isExporting(lean_object* v_opts_998_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_999_ = l_Lean_KVMap_instValueBool;
v___x_1000_ = l_Lean_KVMap_instValueString;
v___x_1001_ = l_Lean_trace_profiler_output;
v___x_1002_ = l_Lean_Option_get_x3f___redArg(v___x_1000_, v_opts_998_, v___x_1001_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = l_Lean_trace_profiler_serve;
v___x_1004_ = l_Lean_Option_get___redArg(v___x_999_, v_opts_998_, v___x_1003_);
v___x_1005_ = lean_unbox(v___x_1004_);
lean_dec(v___x_1004_);
return v___x_1005_;
}
else
{
uint8_t v___x_1006_; 
lean_dec_ref(v___x_1002_);
v___x_1006_ = 1;
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_isExporting___boxed(lean_object* v_opts_1007_){
_start:
{
uint8_t v_res_1008_; lean_object* v_r_1009_; 
v_res_1008_ = l_Lean_trace_profiler_isExporting(v_opts_1007_);
lean_dec_ref(v_opts_1007_);
v_r_1009_ = lean_box(v_res_1008_);
return v_r_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1029_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1030_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1031_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1032_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_1029_, v___x_1030_, v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
return v_res_1034_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1035_; double v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(1000000000u);
v___x_1036_ = lean_float_of_nat(v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object* v_toApplicative_1037_, lean_object* v_start_1038_, lean_object* v_a_1039_, lean_object* v_stop_1040_){
_start:
{
lean_object* v_toPure_1041_; double v___x_1042_; double v___x_1043_; double v___x_1044_; double v___x_1045_; double v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_toPure_1041_ = lean_ctor_get(v_toApplicative_1037_, 1);
lean_inc(v_toPure_1041_);
lean_dec_ref(v_toApplicative_1037_);
v___x_1042_ = lean_float_of_nat(v_start_1038_);
v___x_1043_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1044_ = lean_float_div(v___x_1042_, v___x_1043_);
v___x_1045_ = lean_float_of_nat(v_stop_1040_);
v___x_1046_ = lean_float_div(v___x_1045_, v___x_1043_);
v___x_1047_ = lean_box_float(v___x_1044_);
v___x_1048_ = lean_box_float(v___x_1046_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_a_1039_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_apply_2(v_toPure_1041_, lean_box(0), v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object* v_toApplicative_1052_, lean_object* v_start_1053_, lean_object* v_toBind_1054_, lean_object* v___x_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___f_1057_; lean_object* v___x_1058_; 
v___f_1057_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1057_, 0, v_toApplicative_1052_);
lean_closure_set(v___f_1057_, 1, v_start_1053_);
lean_closure_set(v___f_1057_, 2, v_a_1056_);
v___x_1058_ = lean_apply_4(v_toBind_1054_, lean_box(0), lean_box(0), v___x_1055_, v___f_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object* v_toApplicative_1059_, lean_object* v_toBind_1060_, lean_object* v___x_1061_, lean_object* v_act_1062_, lean_object* v_start_1063_){
_start:
{
lean_object* v___f_1064_; lean_object* v___x_1065_; 
lean_inc(v_toBind_1060_);
v___f_1064_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1064_, 0, v_toApplicative_1059_);
lean_closure_set(v___f_1064_, 1, v_start_1063_);
lean_closure_set(v___f_1064_, 2, v_toBind_1060_);
lean_closure_set(v___f_1064_, 3, v___x_1061_);
v___x_1065_ = lean_apply_4(v_toBind_1060_, lean_box(0), lean_box(0), v_act_1062_, v___f_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object* v_toApplicative_1066_, lean_object* v_start_1067_, lean_object* v_a_1068_, lean_object* v_stop_1069_){
_start:
{
lean_object* v_toPure_1070_; double v___x_1071_; double v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_toPure_1070_ = lean_ctor_get(v_toApplicative_1066_, 1);
lean_inc(v_toPure_1070_);
lean_dec_ref(v_toApplicative_1066_);
v___x_1071_ = lean_float_of_nat(v_start_1067_);
v___x_1072_ = lean_float_of_nat(v_stop_1069_);
v___x_1073_ = lean_box_float(v___x_1071_);
v___x_1074_ = lean_box_float(v___x_1072_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_a_1068_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_apply_2(v_toPure_1070_, lean_box(0), v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object* v_toApplicative_1078_, lean_object* v_start_1079_, lean_object* v_toBind_1080_, lean_object* v___x_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v___f_1083_; lean_object* v___x_1084_; 
v___f_1083_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1083_, 0, v_toApplicative_1078_);
lean_closure_set(v___f_1083_, 1, v_start_1079_);
lean_closure_set(v___f_1083_, 2, v_a_1082_);
v___x_1084_ = lean_apply_4(v_toBind_1080_, lean_box(0), lean_box(0), v___x_1081_, v___f_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object* v_toApplicative_1085_, lean_object* v_toBind_1086_, lean_object* v___x_1087_, lean_object* v_act_1088_, lean_object* v_start_1089_){
_start:
{
lean_object* v___f_1090_; lean_object* v___x_1091_; 
lean_inc(v_toBind_1086_);
v___f_1090_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1090_, 0, v_toApplicative_1085_);
lean_closure_set(v___f_1090_, 1, v_start_1089_);
lean_closure_set(v___f_1090_, 2, v_toBind_1086_);
lean_closure_set(v___f_1090_, 3, v___x_1087_);
v___x_1091_ = lean_apply_4(v_toBind_1086_, lean_box(0), lean_box(0), v_act_1088_, v___f_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_opts_1096_, lean_object* v_act_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1098_ = l_Lean_KVMap_instValueBool;
v___x_1099_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1100_ = l_Lean_Option_get___redArg(v___x_1098_, v_opts_1096_, v___x_1099_);
v___x_1101_ = lean_unbox(v___x_1100_);
lean_dec(v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v_toApplicative_1102_; lean_object* v_toBind_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; 
v_toApplicative_1102_ = lean_ctor_get(v_inst_1094_, 0);
lean_inc_ref(v_toApplicative_1102_);
v_toBind_1103_ = lean_ctor_get(v_inst_1094_, 1);
lean_inc_n(v_toBind_1103_, 2);
lean_dec_ref(v_inst_1094_);
v___x_1104_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1105_ = lean_apply_2(v_inst_1095_, lean_box(0), v___x_1104_);
lean_inc(v___x_1105_);
v___f_1106_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1106_, 0, v_toApplicative_1102_);
lean_closure_set(v___f_1106_, 1, v_toBind_1103_);
lean_closure_set(v___f_1106_, 2, v___x_1105_);
lean_closure_set(v___f_1106_, 3, v_act_1097_);
v___x_1107_ = lean_apply_4(v_toBind_1103_, lean_box(0), lean_box(0), v___x_1105_, v___f_1106_);
return v___x_1107_;
}
else
{
lean_object* v_toApplicative_1108_; lean_object* v_toBind_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___f_1112_; lean_object* v___x_1113_; 
v_toApplicative_1108_ = lean_ctor_get(v_inst_1094_, 0);
lean_inc_ref(v_toApplicative_1108_);
v_toBind_1109_ = lean_ctor_get(v_inst_1094_, 1);
lean_inc_n(v_toBind_1109_, 2);
lean_dec_ref(v_inst_1094_);
v___x_1110_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1111_ = lean_apply_2(v_inst_1095_, lean_box(0), v___x_1110_);
lean_inc(v___x_1111_);
v___f_1112_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1112_, 0, v_toApplicative_1108_);
lean_closure_set(v___f_1112_, 1, v_toBind_1109_);
lean_closure_set(v___f_1112_, 2, v___x_1111_);
lean_closure_set(v___f_1112_, 3, v_act_1097_);
v___x_1113_ = lean_apply_4(v_toBind_1109_, lean_box(0), lean_box(0), v___x_1111_, v___f_1112_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_opts_1116_, lean_object* v_act_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(v_inst_1114_, v_inst_1115_, v_opts_1116_, v_act_1117_);
lean_dec_ref(v_opts_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object* v_00_u03b1_1119_, lean_object* v_m_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_opts_1123_, lean_object* v_act_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1125_ = l_Lean_KVMap_instValueBool;
v___x_1126_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1127_ = l_Lean_Option_get___redArg(v___x_1125_, v_opts_1123_, v___x_1126_);
v___x_1128_ = lean_unbox(v___x_1127_);
lean_dec(v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v_toApplicative_1129_; lean_object* v_toBind_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; 
v_toApplicative_1129_ = lean_ctor_get(v_inst_1121_, 0);
lean_inc_ref(v_toApplicative_1129_);
v_toBind_1130_ = lean_ctor_get(v_inst_1121_, 1);
lean_inc_n(v_toBind_1130_, 2);
lean_dec_ref(v_inst_1121_);
v___x_1131_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1132_ = lean_apply_2(v_inst_1122_, lean_box(0), v___x_1131_);
lean_inc(v___x_1132_);
v___f_1133_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1133_, 0, v_toApplicative_1129_);
lean_closure_set(v___f_1133_, 1, v_toBind_1130_);
lean_closure_set(v___f_1133_, 2, v___x_1132_);
lean_closure_set(v___f_1133_, 3, v_act_1124_);
v___x_1134_ = lean_apply_4(v_toBind_1130_, lean_box(0), lean_box(0), v___x_1132_, v___f_1133_);
return v___x_1134_;
}
else
{
lean_object* v_toApplicative_1135_; lean_object* v_toBind_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; 
v_toApplicative_1135_ = lean_ctor_get(v_inst_1121_, 0);
lean_inc_ref(v_toApplicative_1135_);
v_toBind_1136_ = lean_ctor_get(v_inst_1121_, 1);
lean_inc_n(v_toBind_1136_, 2);
lean_dec_ref(v_inst_1121_);
v___x_1137_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1138_ = lean_apply_2(v_inst_1122_, lean_box(0), v___x_1137_);
lean_inc(v___x_1138_);
v___f_1139_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1139_, 0, v_toApplicative_1135_);
lean_closure_set(v___f_1139_, 1, v_toBind_1136_);
lean_closure_set(v___f_1139_, 2, v___x_1138_);
lean_closure_set(v___f_1139_, 3, v_act_1124_);
v___x_1140_ = lean_apply_4(v_toBind_1136_, lean_box(0), lean_box(0), v___x_1138_, v___f_1139_);
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_m_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_opts_1145_, lean_object* v_act_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(v_00_u03b1_1141_, v_m_1142_, v_inst_1143_, v_inst_1144_, v_opts_1145_, v_act_1146_);
lean_dec_ref(v_opts_1145_);
return v_res_1147_;
}
}
static double _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0(void){
_start:
{
lean_object* v___x_1148_; double v___x_1149_; 
v___x_1148_ = lean_unsigned_to_nat(1000u);
v___x_1149_ = lean_float_of_nat(v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object* v_o_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1151_ = l_Lean_KVMap_instValueBool;
v___x_1152_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1153_ = l_Lean_Option_get___redArg(v___x_1151_, v_o_1150_, v___x_1152_);
v___x_1154_ = lean_unbox(v___x_1153_);
lean_dec(v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; double v___x_1158_; double v___x_1159_; double v___x_1160_; 
v___x_1155_ = l_Lean_KVMap_instValueNat;
v___x_1156_ = l_Lean_trace_profiler_threshold;
v___x_1157_ = l_Lean_Option_get___redArg(v___x_1155_, v_o_1150_, v___x_1156_);
v___x_1158_ = lean_float_of_nat(v___x_1157_);
v___x_1159_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1160_ = lean_float_div(v___x_1158_, v___x_1159_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; double v___x_1164_; 
v___x_1161_ = l_Lean_KVMap_instValueNat;
v___x_1162_ = l_Lean_trace_profiler_threshold;
v___x_1163_ = l_Lean_Option_get___redArg(v___x_1161_, v_o_1150_, v___x_1162_);
v___x_1164_ = lean_float_of_nat(v___x_1163_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object* v_o_1165_){
_start:
{
double v_res_1166_; lean_object* v_r_1167_; 
v_res_1166_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1165_);
lean_dec_ref(v_o_1165_);
v_r_1167_ = lean_box_float(v_res_1166_);
return v_r_1167_;
}
}
static lean_object* _init_l_Lean_instMonadAlwaysExceptEIO___closed__0(void){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object* v_00_u03b5_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___closed__0, &l_Lean_instMonadAlwaysExceptEIO___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___closed__0);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object* v_inst_1171_, lean_object* v_always_1172_){
_start:
{
lean_object* v___f_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; 
lean_inc_ref(v_always_1172_);
v___f_1173_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1173_, 0, v_always_1172_);
lean_closure_set(v___f_1173_, 1, v_inst_1171_);
v___f_1174_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_1174_, 0, v_always_1172_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___f_1173_);
lean_ctor_set(v___x_1175_, 1, v___f_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object* v_m_1176_, lean_object* v_inst_1177_, lean_object* v_00_u03b5_1178_, lean_object* v_00_u03c3_1179_, lean_object* v_always_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_1177_, v_always_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object* v_always_1182_){
_start:
{
lean_object* v___f_1183_; lean_object* v___f_1184_; lean_object* v___x_1185_; 
lean_inc_ref(v_always_1182_);
v___f_1183_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1183_, 0, v_always_1182_);
v___f_1184_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1184_, 0, v_always_1182_);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___f_1183_);
lean_ctor_set(v___x_1185_, 1, v___f_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object* v_m_1186_, lean_object* v_00_u03b5_1187_, lean_object* v_00_u03c9_1188_, lean_object* v_00_u03c3_1189_, lean_object* v_always_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object* v_always_1192_){
_start:
{
lean_object* v___f_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; 
lean_inc_ref(v_always_1192_);
v___f_1193_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1193_, 0, v_always_1192_);
v___f_1194_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1194_, 0, v_always_1192_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___f_1193_);
lean_ctor_set(v___x_1195_, 1, v___f_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object* v_m_1196_, lean_object* v_00_u03b5_1197_, lean_object* v_00_u03c1_1198_, lean_object* v_always_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object* v_always_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1202_, v_inst_1203_, v_inst_1204_, v_always_1201_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object* v_00_u03b1_1206_, lean_object* v_m_1207_, lean_object* v_00_u03b5_1208_, lean_object* v_00_u03c9_1209_, lean_object* v_00_u03b2_1210_, lean_object* v_always_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1212_, v_inst_1213_, v_inst_1214_, v_always_1211_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t v_x_1222_){
_start:
{
switch(v_x_1222_)
{
case 0:
{
lean_object* v___x_1223_; 
v___x_1223_ = ((lean_object*)(l_Lean_checkEmoji___closed__0));
return v___x_1223_;
}
case 1:
{
lean_object* v___x_1224_; 
v___x_1224_ = ((lean_object*)(l_Lean_crossEmoji___closed__0));
return v___x_1224_;
}
default: 
{
lean_object* v___x_1225_; 
v___x_1225_ = ((lean_object*)(l_Lean_bombEmoji___closed__0));
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object* v_x_1226_){
_start:
{
uint8_t v_x_31__boxed_1227_; lean_object* v_res_1228_; 
v_x_31__boxed_1227_ = lean_unbox(v_x_1226_);
v_res_1228_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_1227_);
return v_res_1228_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___lam__0(lean_object* v_x_1229_){
_start:
{
if (lean_obj_tag(v_x_1229_) == 0)
{
uint8_t v___x_1230_; 
v___x_1230_ = 2;
return v___x_1230_;
}
else
{
lean_object* v_a_1231_; uint8_t v___x_1232_; 
v_a_1231_ = lean_ctor_get(v_x_1229_, 0);
v___x_1232_ = lean_unbox(v_a_1231_);
if (v___x_1232_ == 0)
{
uint8_t v___x_1233_; 
v___x_1233_ = 1;
return v___x_1233_;
}
else
{
uint8_t v___x_1234_; 
v___x_1234_ = 0;
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object* v_x_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_Lean_instExceptToTraceResultBool___lam__0(v_x_1235_);
lean_dec_ref(v_x_1235_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object* v_00_u03b5_1239_){
_start:
{
lean_object* v___f_1240_; 
v___f_1240_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___closed__0));
return v___f_1240_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___lam__0(lean_object* v_x_1241_){
_start:
{
if (lean_obj_tag(v_x_1241_) == 0)
{
uint8_t v___x_1242_; 
v___x_1242_ = 2;
return v___x_1242_;
}
else
{
lean_object* v_a_1243_; 
v_a_1243_ = lean_ctor_get(v_x_1241_, 0);
if (lean_obj_tag(v_a_1243_) == 0)
{
uint8_t v___x_1244_; 
v___x_1244_ = 1;
return v___x_1244_;
}
else
{
uint8_t v___x_1245_; 
v___x_1245_ = 0;
return v___x_1245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object* v_x_1246_){
_start:
{
uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_res_1247_ = l_Lean_instExceptToTraceResultOption___lam__0(v_x_1246_);
lean_dec_ref(v_x_1246_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object* v_00_u03b1_1250_, lean_object* v_00_u03b5_1251_){
_start:
{
lean_object* v___f_1252_; 
v___f_1252_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___closed__0));
return v___f_1252_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object* v_x_1253_){
_start:
{
if (lean_obj_tag(v_x_1253_) == 0)
{
uint8_t v___x_1254_; 
v___x_1254_ = 2;
return v___x_1254_;
}
else
{
uint8_t v___x_1255_; 
v___x_1255_ = 0;
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object* v_x_1256_){
_start:
{
uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_res_1257_ = l_Lean_instExceptToTraceResult___lam__0(v_x_1256_);
lean_dec_ref(v_x_1256_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object* v_00_u03b1_1260_, lean_object* v_00_u03b5_1261_){
_start:
{
lean_object* v___f_1262_; 
v___f_1262_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
return v___f_1262_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___redArg(lean_object* v_inst_1263_, lean_object* v_e_1264_){
_start:
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = lean_apply_1(v_inst_1263_, v_e_1264_);
v___x_1266_ = lean_unbox(v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___redArg___boxed(lean_object* v_inst_1267_, lean_object* v_e_1268_){
_start:
{
uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = l_Except_toTraceResult___redArg(v_inst_1267_, v_e_1268_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult(lean_object* v_00_u03b1_1271_, lean_object* v_00_u03b5_1272_, lean_object* v_inst_1273_, lean_object* v_e_1274_){
_start:
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_apply_1(v_inst_1273_, v_e_1274_);
v___x_1276_ = lean_unbox(v___x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___boxed(lean_object* v_00_u03b1_1277_, lean_object* v_00_u03b5_1278_, lean_object* v_inst_1279_, lean_object* v_e_1280_){
_start:
{
uint8_t v_res_1281_; lean_object* v_r_1282_; 
v_res_1281_ = l_Except_toTraceResult(v_00_u03b1_1277_, v_00_u03b5_1278_, v_inst_1279_, v_e_1280_);
v_r_1282_ = lean_box(v_res_1281_);
return v_r_1282_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object* v_inst_1286_, lean_object* v_x_1287_){
_start:
{
lean_object* v_toApplicative_1288_; lean_object* v_toPure_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_toApplicative_1288_ = lean_ctor_get(v_inst_1286_, 0);
lean_inc_ref(v_toApplicative_1288_);
lean_dec_ref(v_inst_1286_);
v_toPure_1289_ = lean_ctor_get(v_toApplicative_1288_, 1);
lean_inc(v_toPure_1289_);
lean_dec_ref(v_toApplicative_1288_);
v___x_1290_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1);
v___x_1291_ = lean_apply_2(v_toPure_1289_, lean_box(0), v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(lean_object* v_inst_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(v_inst_1292_, v_x_1293_);
lean_dec(v_x_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object* v_oldTraces_1295_, lean_object* v_s_1296_){
_start:
{
uint64_t v_tid_1297_; lean_object* v_traces_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1306_; 
v_tid_1297_ = lean_ctor_get_uint64(v_s_1296_, sizeof(void*)*1);
v_traces_1298_ = lean_ctor_get(v_s_1296_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_s_1296_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1300_ = v_s_1296_;
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_traces_1298_);
lean_dec(v_s_1296_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1295_, v_traces_1298_);
lean_dec_ref(v_traces_1298_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1302_);
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
lean_ctor_set_uint64(v_reuseFailAlloc_1305_, sizeof(void*)*1, v_tid_1297_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object* v_always_1307_, lean_object* v_inst_1308_, lean_object* v_fst_1309_, lean_object* v_____r_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1307_);
v___x_1312_ = l_MonadExcept_ofExcept___redArg(v_inst_1308_, v___x_1311_, v_fst_1309_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object* v_inst_1313_, lean_object* v___x_1314_, lean_object* v_fst_1315_, lean_object* v_____r_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_MonadExcept_ofExcept___redArg(v_inst_1313_, v___x_1314_, v_fst_1315_);
return v___x_1317_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0));
v___x_1320_ = l_Lean_stringToMessageData(v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object* v_inst_1321_, lean_object* v_fst_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_oldTraces_1327_, lean_object* v_ref_1328_, lean_object* v_toBind_1329_, lean_object* v___f_1330_, lean_object* v_cls_1331_, uint8_t v_collapsed_1332_, lean_object* v_tag_1333_, uint8_t v___x_1334_, double v_fst_1335_, double v_snd_1336_, lean_object* v_m_1337_){
_start:
{
lean_object* v_result_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v_m_1344_; lean_object* v_data_1346_; lean_object* v___x_1349_; double v___x_1350_; lean_object* v_data_1351_; 
v_result_1338_ = lean_apply_1(v_inst_1321_, v_fst_1322_);
v___x_1339_ = lean_unbox(v_result_1338_);
v___x_1340_ = l_Lean_TraceResult_toEmoji(v___x_1339_);
v___x_1341_ = l_Lean_stringToMessageData(v___x_1340_);
v___x_1342_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
v___x_1343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v_m_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_m_1344_, 0, v___x_1343_);
lean_ctor_set(v_m_1344_, 1, v_m_1337_);
v___x_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1349_, 0, v_result_1338_);
v___x_1350_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_1333_);
lean_inc_ref(v___x_1349_);
lean_inc(v_cls_1331_);
v_data_1351_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1351_, 0, v_cls_1331_);
lean_ctor_set(v_data_1351_, 1, v___x_1349_);
lean_ctor_set(v_data_1351_, 2, v_tag_1333_);
lean_ctor_set_float(v_data_1351_, sizeof(void*)*3, v___x_1350_);
lean_ctor_set_float(v_data_1351_, sizeof(void*)*3 + 8, v___x_1350_);
lean_ctor_set_uint8(v_data_1351_, sizeof(void*)*3 + 16, v_collapsed_1332_);
if (v___x_1334_ == 0)
{
lean_dec_ref(v___x_1349_);
lean_dec_ref(v_tag_1333_);
lean_dec(v_cls_1331_);
v_data_1346_ = v_data_1351_;
goto v___jp_1345_;
}
else
{
lean_object* v_data_1352_; 
lean_dec_ref(v_data_1351_);
v_data_1352_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1352_, 0, v_cls_1331_);
lean_ctor_set(v_data_1352_, 1, v___x_1349_);
lean_ctor_set(v_data_1352_, 2, v_tag_1333_);
lean_ctor_set_float(v_data_1352_, sizeof(void*)*3, v_fst_1335_);
lean_ctor_set_float(v_data_1352_, sizeof(void*)*3 + 8, v_snd_1336_);
lean_ctor_set_uint8(v_data_1352_, sizeof(void*)*3 + 16, v_collapsed_1332_);
v_data_1346_ = v_data_1352_;
goto v___jp_1345_;
}
v___jp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_1323_, v_inst_1324_, v_inst_1325_, v_inst_1326_, v_oldTraces_1327_, v_data_1346_, v_ref_1328_, v_m_1344_);
v___x_1348_ = lean_apply_4(v_toBind_1329_, lean_box(0), lean_box(0), v___x_1347_, v___f_1330_);
return v___x_1348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_1353_ = _args[0];
lean_object* v_fst_1354_ = _args[1];
lean_object* v_inst_1355_ = _args[2];
lean_object* v_inst_1356_ = _args[3];
lean_object* v_inst_1357_ = _args[4];
lean_object* v_inst_1358_ = _args[5];
lean_object* v_oldTraces_1359_ = _args[6];
lean_object* v_ref_1360_ = _args[7];
lean_object* v_toBind_1361_ = _args[8];
lean_object* v___f_1362_ = _args[9];
lean_object* v_cls_1363_ = _args[10];
lean_object* v_collapsed_1364_ = _args[11];
lean_object* v_tag_1365_ = _args[12];
lean_object* v___x_1366_ = _args[13];
lean_object* v_fst_1367_ = _args[14];
lean_object* v_snd_1368_ = _args[15];
lean_object* v_m_1369_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1370_; uint8_t v___x_677__boxed_1371_; double v_fst_678__boxed_1372_; double v_snd_679__boxed_1373_; lean_object* v_res_1374_; 
v_collapsed_boxed_1370_ = lean_unbox(v_collapsed_1364_);
v___x_677__boxed_1371_ = lean_unbox(v___x_1366_);
v_fst_678__boxed_1372_ = lean_unbox_float(v_fst_1367_);
lean_dec_ref(v_fst_1367_);
v_snd_679__boxed_1373_ = lean_unbox_float(v_snd_1368_);
lean_dec_ref(v_snd_1368_);
v_res_1374_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1353_, v_fst_1354_, v_inst_1355_, v_inst_1356_, v_inst_1357_, v_inst_1358_, v_oldTraces_1359_, v_ref_1360_, v_toBind_1361_, v___f_1362_, v_cls_1363_, v_collapsed_boxed_1370_, v_tag_1365_, v___x_677__boxed_1371_, v_fst_678__boxed_1372_, v_snd_679__boxed_1373_, v_m_1369_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(lean_object* v_always_1375_, lean_object* v_inst_1376_, lean_object* v_fst_1377_, lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_oldTraces_1382_, lean_object* v_toBind_1383_, lean_object* v_cls_1384_, uint8_t v_collapsed_1385_, lean_object* v_tag_1386_, uint8_t v___x_1387_, double v_fst_1388_, double v_snd_1389_, lean_object* v_msg_1390_, lean_object* v___f_1391_, lean_object* v_ref_1392_){
_start:
{
lean_object* v___x_1393_; lean_object* v_tryCatch_1394_; lean_object* v___f_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_inc_ref(v_always_1375_);
v___x_1393_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1375_);
v_tryCatch_1394_ = lean_ctor_get(v_always_1375_, 1);
lean_inc(v_tryCatch_1394_);
lean_dec_ref(v_always_1375_);
lean_inc_ref_n(v_fst_1377_, 2);
lean_inc_ref(v_inst_1376_);
v___f_1395_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1395_, 0, v_inst_1376_);
lean_closure_set(v___f_1395_, 1, v___x_1393_);
lean_closure_set(v___f_1395_, 2, v_fst_1377_);
v___x_1396_ = lean_box(v_collapsed_1385_);
v___x_1397_ = lean_box(v___x_1387_);
v___x_1398_ = lean_box_float(v_fst_1388_);
v___x_1399_ = lean_box_float(v_snd_1389_);
lean_inc(v_toBind_1383_);
v___f_1400_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1400_, 0, v_inst_1378_);
lean_closure_set(v___f_1400_, 1, v_fst_1377_);
lean_closure_set(v___f_1400_, 2, v_inst_1376_);
lean_closure_set(v___f_1400_, 3, v_inst_1379_);
lean_closure_set(v___f_1400_, 4, v_inst_1380_);
lean_closure_set(v___f_1400_, 5, v_inst_1381_);
lean_closure_set(v___f_1400_, 6, v_oldTraces_1382_);
lean_closure_set(v___f_1400_, 7, v_ref_1392_);
lean_closure_set(v___f_1400_, 8, v_toBind_1383_);
lean_closure_set(v___f_1400_, 9, v___f_1395_);
lean_closure_set(v___f_1400_, 10, v_cls_1384_);
lean_closure_set(v___f_1400_, 11, v___x_1396_);
lean_closure_set(v___f_1400_, 12, v_tag_1386_);
lean_closure_set(v___f_1400_, 13, v___x_1397_);
lean_closure_set(v___f_1400_, 14, v___x_1398_);
lean_closure_set(v___f_1400_, 15, v___x_1399_);
v___x_1401_ = lean_apply_1(v_msg_1390_, v_fst_1377_);
v___x_1402_ = lean_apply_3(v_tryCatch_1394_, lean_box(0), v___x_1401_, v___f_1391_);
v___x_1403_ = lean_apply_4(v_toBind_1383_, lean_box(0), lean_box(0), v___x_1402_, v___f_1400_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_always_1404_ = _args[0];
lean_object* v_inst_1405_ = _args[1];
lean_object* v_fst_1406_ = _args[2];
lean_object* v_inst_1407_ = _args[3];
lean_object* v_inst_1408_ = _args[4];
lean_object* v_inst_1409_ = _args[5];
lean_object* v_inst_1410_ = _args[6];
lean_object* v_oldTraces_1411_ = _args[7];
lean_object* v_toBind_1412_ = _args[8];
lean_object* v_cls_1413_ = _args[9];
lean_object* v_collapsed_1414_ = _args[10];
lean_object* v_tag_1415_ = _args[11];
lean_object* v___x_1416_ = _args[12];
lean_object* v_fst_1417_ = _args[13];
lean_object* v_snd_1418_ = _args[14];
lean_object* v_msg_1419_ = _args[15];
lean_object* v___f_1420_ = _args[16];
lean_object* v_ref_1421_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_1422_; uint8_t v___x_729__boxed_1423_; double v_fst_730__boxed_1424_; double v_snd_731__boxed_1425_; lean_object* v_res_1426_; 
v_collapsed_boxed_1422_ = lean_unbox(v_collapsed_1414_);
v___x_729__boxed_1423_ = lean_unbox(v___x_1416_);
v_fst_730__boxed_1424_ = lean_unbox_float(v_fst_1417_);
lean_dec_ref(v_fst_1417_);
v_snd_731__boxed_1425_ = lean_unbox_float(v_snd_1418_);
lean_dec_ref(v_snd_1418_);
v_res_1426_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(v_always_1404_, v_inst_1405_, v_fst_1406_, v_inst_1407_, v_inst_1408_, v_inst_1409_, v_inst_1410_, v_oldTraces_1411_, v_toBind_1412_, v_cls_1413_, v_collapsed_boxed_1422_, v_tag_1415_, v___x_729__boxed_1423_, v_fst_730__boxed_1424_, v_snd_731__boxed_1425_, v_msg_1419_, v___f_1420_, v_ref_1421_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_inst_1430_, lean_object* v_always_1431_, lean_object* v_inst_1432_, lean_object* v_cls_1433_, uint8_t v_collapsed_1434_, lean_object* v_tag_1435_, lean_object* v_opts_1436_, uint8_t v_clsEnabled_1437_, lean_object* v_oldTraces_1438_, lean_object* v_msg_1439_, lean_object* v_resStartStop_1440_){
_start:
{
lean_object* v___x_1441_; lean_object* v_snd_1442_; lean_object* v_fst_1443_; lean_object* v_fst_1444_; lean_object* v_snd_1445_; lean_object* v___f_1446_; lean_object* v___f_1447_; lean_object* v___f_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___y_1458_; double v___y_1464_; uint8_t v___x_1469_; 
v___x_1441_ = l_Lean_KVMap_instValueBool;
v_snd_1442_ = lean_ctor_get(v_resStartStop_1440_, 1);
lean_inc(v_snd_1442_);
v_fst_1443_ = lean_ctor_get(v_resStartStop_1440_, 0);
lean_inc_n(v_fst_1443_, 2);
lean_dec_ref(v_resStartStop_1440_);
v_fst_1444_ = lean_ctor_get(v_snd_1442_, 0);
lean_inc(v_fst_1444_);
v_snd_1445_ = lean_ctor_get(v_snd_1442_, 1);
lean_inc(v_snd_1445_);
lean_dec(v_snd_1442_);
lean_inc_ref_n(v_inst_1427_, 2);
v___f_1446_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1446_, 0, v_inst_1427_);
lean_inc_ref(v_oldTraces_1438_);
v___f_1447_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1447_, 0, v_oldTraces_1438_);
lean_inc_ref(v_always_1431_);
v___f_1448_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1448_, 0, v_always_1431_);
lean_closure_set(v___f_1448_, 1, v_inst_1427_);
lean_closure_set(v___f_1448_, 2, v_fst_1443_);
v___x_1449_ = l_Lean_trace_profiler;
v___x_1450_ = l_Lean_Option_get___redArg(v___x_1441_, v_opts_1436_, v___x_1449_);
v___x_1469_ = lean_unbox(v___x_1450_);
if (v___x_1469_ == 0)
{
uint8_t v___x_1470_; 
v___x_1470_ = lean_unbox(v___x_1450_);
v___y_1458_ = v___x_1470_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1472_ = l_Lean_Option_get___redArg(v___x_1441_, v_opts_1436_, v___x_1471_);
v___x_1473_ = lean_unbox(v___x_1472_);
lean_dec(v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; double v___x_1477_; double v___x_1478_; double v___x_1479_; 
v___x_1474_ = l_Lean_KVMap_instValueNat;
v___x_1475_ = l_Lean_trace_profiler_threshold;
v___x_1476_ = l_Lean_Option_get___redArg(v___x_1474_, v_opts_1436_, v___x_1475_);
v___x_1477_ = lean_float_of_nat(v___x_1476_);
v___x_1478_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1479_ = lean_float_div(v___x_1477_, v___x_1478_);
v___y_1464_ = v___x_1479_;
goto v___jp_1463_;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; double v___x_1483_; 
v___x_1480_ = l_Lean_KVMap_instValueNat;
v___x_1481_ = l_Lean_trace_profiler_threshold;
v___x_1482_ = l_Lean_Option_get___redArg(v___x_1480_, v_opts_1436_, v___x_1481_);
v___x_1483_ = lean_float_of_nat(v___x_1482_);
v___y_1464_ = v___x_1483_;
goto v___jp_1463_;
}
}
v___jp_1451_:
{
lean_object* v_toBind_1452_; lean_object* v_getRef_1453_; lean_object* v___x_1454_; lean_object* v___f_1455_; lean_object* v___x_1456_; 
v_toBind_1452_ = lean_ctor_get(v_inst_1427_, 1);
lean_inc_n(v_toBind_1452_, 2);
v_getRef_1453_ = lean_ctor_get(v_inst_1429_, 0);
lean_inc(v_getRef_1453_);
v___x_1454_ = lean_box(v_collapsed_1434_);
v___f_1455_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed), 18, 17);
lean_closure_set(v___f_1455_, 0, v_always_1431_);
lean_closure_set(v___f_1455_, 1, v_inst_1427_);
lean_closure_set(v___f_1455_, 2, v_fst_1443_);
lean_closure_set(v___f_1455_, 3, v_inst_1432_);
lean_closure_set(v___f_1455_, 4, v_inst_1428_);
lean_closure_set(v___f_1455_, 5, v_inst_1429_);
lean_closure_set(v___f_1455_, 6, v_inst_1430_);
lean_closure_set(v___f_1455_, 7, v_oldTraces_1438_);
lean_closure_set(v___f_1455_, 8, v_toBind_1452_);
lean_closure_set(v___f_1455_, 9, v_cls_1433_);
lean_closure_set(v___f_1455_, 10, v___x_1454_);
lean_closure_set(v___f_1455_, 11, v_tag_1435_);
lean_closure_set(v___f_1455_, 12, v___x_1450_);
lean_closure_set(v___f_1455_, 13, v_fst_1444_);
lean_closure_set(v___f_1455_, 14, v_snd_1445_);
lean_closure_set(v___f_1455_, 15, v_msg_1439_);
lean_closure_set(v___f_1455_, 16, v___f_1446_);
v___x_1456_ = lean_apply_4(v_toBind_1452_, lean_box(0), lean_box(0), v_getRef_1453_, v___f_1455_);
return v___x_1456_;
}
v___jp_1457_:
{
if (v_clsEnabled_1437_ == 0)
{
if (v___y_1458_ == 0)
{
lean_object* v_toBind_1459_; lean_object* v_modifyTraceState_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec(v___x_1450_);
lean_dec_ref(v___f_1446_);
lean_dec(v_snd_1445_);
lean_dec(v_fst_1444_);
lean_dec(v_fst_1443_);
lean_dec(v_msg_1439_);
lean_dec_ref(v_oldTraces_1438_);
lean_dec_ref(v_tag_1435_);
lean_dec(v_cls_1433_);
lean_dec_ref(v_inst_1432_);
lean_dec_ref(v_always_1431_);
lean_dec(v_inst_1430_);
lean_dec_ref(v_inst_1429_);
v_toBind_1459_ = lean_ctor_get(v_inst_1427_, 1);
lean_inc(v_toBind_1459_);
lean_dec_ref(v_inst_1427_);
v_modifyTraceState_1460_ = lean_ctor_get(v_inst_1428_, 0);
lean_inc(v_modifyTraceState_1460_);
lean_dec_ref(v_inst_1428_);
v___x_1461_ = lean_apply_1(v_modifyTraceState_1460_, v___f_1447_);
v___x_1462_ = lean_apply_4(v_toBind_1459_, lean_box(0), lean_box(0), v___x_1461_, v___f_1448_);
return v___x_1462_;
}
else
{
lean_dec_ref(v___f_1448_);
lean_dec_ref(v___f_1447_);
goto v___jp_1451_;
}
}
else
{
lean_dec_ref(v___f_1448_);
lean_dec_ref(v___f_1447_);
goto v___jp_1451_;
}
}
v___jp_1463_:
{
double v___x_1465_; double v___x_1466_; double v___x_1467_; uint8_t v___x_1468_; 
v___x_1465_ = lean_unbox_float(v_snd_1445_);
v___x_1466_ = lean_unbox_float(v_fst_1444_);
v___x_1467_ = lean_float_sub(v___x_1465_, v___x_1466_);
v___x_1468_ = lean_float_decLt(v___y_1464_, v___x_1467_);
v___y_1458_ = v___x_1468_;
goto v___jp_1457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_inst_1486_, lean_object* v_inst_1487_, lean_object* v_always_1488_, lean_object* v_inst_1489_, lean_object* v_cls_1490_, lean_object* v_collapsed_1491_, lean_object* v_tag_1492_, lean_object* v_opts_1493_, lean_object* v_clsEnabled_1494_, lean_object* v_oldTraces_1495_, lean_object* v_msg_1496_, lean_object* v_resStartStop_1497_){
_start:
{
uint8_t v_collapsed_boxed_1498_; uint8_t v_clsEnabled_boxed_1499_; lean_object* v_res_1500_; 
v_collapsed_boxed_1498_ = lean_unbox(v_collapsed_1491_);
v_clsEnabled_boxed_1499_ = lean_unbox(v_clsEnabled_1494_);
v_res_1500_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1484_, v_inst_1485_, v_inst_1486_, v_inst_1487_, v_always_1488_, v_inst_1489_, v_cls_1490_, v_collapsed_boxed_1498_, v_tag_1492_, v_opts_1493_, v_clsEnabled_boxed_1499_, v_oldTraces_1495_, v_msg_1496_, v_resStartStop_1497_);
lean_dec_ref(v_opts_1493_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object* v_00_u03b1_1501_, lean_object* v_m_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_00_u03b5_1507_, lean_object* v_always_1508_, lean_object* v_inst_1509_, lean_object* v_cls_1510_, uint8_t v_collapsed_1511_, lean_object* v_tag_1512_, lean_object* v_opts_1513_, uint8_t v_clsEnabled_1514_, lean_object* v_oldTraces_1515_, lean_object* v_msg_1516_, lean_object* v_resStartStop_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1503_, v_inst_1504_, v_inst_1505_, v_inst_1506_, v_always_1508_, v_inst_1509_, v_cls_1510_, v_collapsed_1511_, v_tag_1512_, v_opts_1513_, v_clsEnabled_1514_, v_oldTraces_1515_, v_msg_1516_, v_resStartStop_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_1519_ = _args[0];
lean_object* v_m_1520_ = _args[1];
lean_object* v_inst_1521_ = _args[2];
lean_object* v_inst_1522_ = _args[3];
lean_object* v_inst_1523_ = _args[4];
lean_object* v_inst_1524_ = _args[5];
lean_object* v_00_u03b5_1525_ = _args[6];
lean_object* v_always_1526_ = _args[7];
lean_object* v_inst_1527_ = _args[8];
lean_object* v_cls_1528_ = _args[9];
lean_object* v_collapsed_1529_ = _args[10];
lean_object* v_tag_1530_ = _args[11];
lean_object* v_opts_1531_ = _args[12];
lean_object* v_clsEnabled_1532_ = _args[13];
lean_object* v_oldTraces_1533_ = _args[14];
lean_object* v_msg_1534_ = _args[15];
lean_object* v_resStartStop_1535_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1536_; uint8_t v_clsEnabled_boxed_1537_; lean_object* v_res_1538_; 
v_collapsed_boxed_1536_ = lean_unbox(v_collapsed_1529_);
v_clsEnabled_boxed_1537_ = lean_unbox(v_clsEnabled_1532_);
v_res_1538_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(v_00_u03b1_1519_, v_m_1520_, v_inst_1521_, v_inst_1522_, v_inst_1523_, v_inst_1524_, v_00_u03b5_1525_, v_always_1526_, v_inst_1527_, v_cls_1528_, v_collapsed_boxed_1536_, v_tag_1530_, v_opts_1531_, v_clsEnabled_boxed_1537_, v_oldTraces_1533_, v_msg_1534_, v_resStartStop_1535_);
lean_dec_ref(v_opts_1531_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_inst_1541_, lean_object* v_inst_1542_, lean_object* v_always_1543_, lean_object* v_inst_1544_, lean_object* v_cls_1545_, uint8_t v_collapsed_1546_, lean_object* v_tag_1547_, lean_object* v_opts_1548_, uint8_t v_clsEnabled_1549_, lean_object* v_oldTraces_1550_, lean_object* v_msg_1551_, lean_object* v_resStartStop_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1539_, v_inst_1540_, v_inst_1541_, v_inst_1542_, v_always_1543_, v_inst_1544_, v_cls_1545_, v_collapsed_1546_, v_tag_1547_, v_opts_1548_, v_clsEnabled_1549_, v_oldTraces_1550_, v_msg_1551_, v_resStartStop_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_inst_1556_, lean_object* v_inst_1557_, lean_object* v_always_1558_, lean_object* v_inst_1559_, lean_object* v_cls_1560_, lean_object* v_collapsed_1561_, lean_object* v_tag_1562_, lean_object* v_opts_1563_, lean_object* v_clsEnabled_1564_, lean_object* v_oldTraces_1565_, lean_object* v_msg_1566_, lean_object* v_resStartStop_1567_){
_start:
{
uint8_t v_collapsed_boxed_1568_; uint8_t v_clsEnabled_boxed_1569_; lean_object* v_res_1570_; 
v_collapsed_boxed_1568_ = lean_unbox(v_collapsed_1561_);
v_clsEnabled_boxed_1569_ = lean_unbox(v_clsEnabled_1564_);
v_res_1570_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1554_, v_inst_1555_, v_inst_1556_, v_inst_1557_, v_always_1558_, v_inst_1559_, v_cls_1560_, v_collapsed_boxed_1568_, v_tag_1562_, v_opts_1563_, v_clsEnabled_boxed_1569_, v_oldTraces_1565_, v_msg_1566_, v_resStartStop_1567_);
lean_dec_ref(v_opts_1563_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object* v_toPure_1571_, lean_object* v_ex_1572_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_ex_1572_);
v___x_1574_ = lean_apply_2(v_toPure_1571_, lean_box(0), v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object* v_toPure_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_a_1576_);
v___x_1578_ = lean_apply_2(v_toPure_1575_, lean_box(0), v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object* v_start_1579_, lean_object* v_a_1580_, lean_object* v_toPure_1581_, lean_object* v_stop_1582_){
_start:
{
double v___x_1583_; double v___x_1584_; double v___x_1585_; double v___x_1586_; double v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1583_ = lean_float_of_nat(v_start_1579_);
v___x_1584_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1585_ = lean_float_div(v___x_1583_, v___x_1584_);
v___x_1586_ = lean_float_of_nat(v_stop_1582_);
v___x_1587_ = lean_float_div(v___x_1586_, v___x_1584_);
v___x_1588_ = lean_box_float(v___x_1585_);
v___x_1589_ = lean_box_float(v___x_1587_);
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v_a_1580_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = lean_apply_2(v_toPure_1581_, lean_box(0), v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object* v_start_1593_, lean_object* v_toPure_1594_, lean_object* v_toBind_1595_, lean_object* v___x_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___f_1598_; lean_object* v___x_1599_; 
v___f_1598_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1598_, 0, v_start_1593_);
lean_closure_set(v___f_1598_, 1, v_a_1597_);
lean_closure_set(v___f_1598_, 2, v_toPure_1594_);
v___x_1599_ = lean_apply_4(v_toBind_1595_, lean_box(0), lean_box(0), v___x_1596_, v___f_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object* v_toPure_1600_, lean_object* v_toBind_1601_, lean_object* v___x_1602_, lean_object* v___x_1603_, lean_object* v_start_1604_){
_start:
{
lean_object* v___f_1605_; lean_object* v___x_1606_; 
lean_inc(v_toBind_1601_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1605_, 0, v_start_1604_);
lean_closure_set(v___f_1605_, 1, v_toPure_1600_);
lean_closure_set(v___f_1605_, 2, v_toBind_1601_);
lean_closure_set(v___f_1605_, 3, v___x_1602_);
v___x_1606_ = lean_apply_4(v_toBind_1601_, lean_box(0), lean_box(0), v___x_1603_, v___f_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object* v_start_1607_, lean_object* v_a_1608_, lean_object* v_toPure_1609_, lean_object* v_stop_1610_){
_start:
{
double v___x_1611_; double v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1611_ = lean_float_of_nat(v_start_1607_);
v___x_1612_ = lean_float_of_nat(v_stop_1610_);
v___x_1613_ = lean_box_float(v___x_1611_);
v___x_1614_ = lean_box_float(v___x_1612_);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_a_1608_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_apply_2(v_toPure_1609_, lean_box(0), v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object* v_start_1618_, lean_object* v_toPure_1619_, lean_object* v_toBind_1620_, lean_object* v___x_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v___f_1623_; lean_object* v___x_1624_; 
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__6), 4, 3);
lean_closure_set(v___f_1623_, 0, v_start_1618_);
lean_closure_set(v___f_1623_, 1, v_a_1622_);
lean_closure_set(v___f_1623_, 2, v_toPure_1619_);
v___x_1624_ = lean_apply_4(v_toBind_1620_, lean_box(0), lean_box(0), v___x_1621_, v___f_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object* v_toPure_1625_, lean_object* v_toBind_1626_, lean_object* v___x_1627_, lean_object* v___x_1628_, lean_object* v_start_1629_){
_start:
{
lean_object* v___f_1630_; lean_object* v___x_1631_; 
lean_inc(v_toBind_1626_);
v___f_1630_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1630_, 0, v_start_1629_);
lean_closure_set(v___f_1630_, 1, v_toPure_1625_);
lean_closure_set(v___f_1630_, 2, v_toBind_1626_);
lean_closure_set(v___f_1630_, 3, v___x_1627_);
v___x_1631_ = lean_apply_4(v_toBind_1626_, lean_box(0), lean_box(0), v___x_1628_, v___f_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object* v_always_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_cls_1638_, uint8_t v_collapsed_1639_, lean_object* v_tag_1640_, lean_object* v_opts_1641_, uint8_t v_clsEnabled_1642_, lean_object* v_msg_1643_, lean_object* v_toPure_1644_, lean_object* v_toBind_1645_, lean_object* v_k_1646_, lean_object* v_inst_1647_, lean_object* v_oldTraces_1648_){
_start:
{
lean_object* v_tryCatch_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___f_1652_; lean_object* v___f_1653_; lean_object* v___f_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v_tryCatch_1649_ = lean_ctor_get(v_always_1632_, 1);
lean_inc(v_tryCatch_1649_);
v___x_1650_ = lean_box(v_collapsed_1639_);
v___x_1651_ = lean_box(v_clsEnabled_1642_);
lean_inc_ref(v_opts_1641_);
v___f_1652_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1652_, 0, v_inst_1633_);
lean_closure_set(v___f_1652_, 1, v_inst_1634_);
lean_closure_set(v___f_1652_, 2, v_inst_1635_);
lean_closure_set(v___f_1652_, 3, v_inst_1636_);
lean_closure_set(v___f_1652_, 4, v_always_1632_);
lean_closure_set(v___f_1652_, 5, v_inst_1637_);
lean_closure_set(v___f_1652_, 6, v_cls_1638_);
lean_closure_set(v___f_1652_, 7, v___x_1650_);
lean_closure_set(v___f_1652_, 8, v_tag_1640_);
lean_closure_set(v___f_1652_, 9, v_opts_1641_);
lean_closure_set(v___f_1652_, 10, v___x_1651_);
lean_closure_set(v___f_1652_, 11, v_oldTraces_1648_);
lean_closure_set(v___f_1652_, 12, v_msg_1643_);
lean_inc_n(v_toPure_1644_, 2);
v___f_1653_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1653_, 0, v_toPure_1644_);
v___f_1654_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1654_, 0, v_toPure_1644_);
lean_inc(v_toBind_1645_);
v___x_1655_ = lean_apply_4(v_toBind_1645_, lean_box(0), lean_box(0), v_k_1646_, v___f_1654_);
v___x_1656_ = lean_apply_3(v_tryCatch_1649_, lean_box(0), v___x_1655_, v___f_1653_);
v___x_1657_ = l_Lean_KVMap_instValueBool;
v___x_1658_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1659_ = l_Lean_Option_get___redArg(v___x_1657_, v_opts_1641_, v___x_1658_);
lean_dec_ref(v_opts_1641_);
v___x_1660_ = lean_unbox(v___x_1659_);
lean_dec(v___x_1659_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___f_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1661_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1662_ = lean_apply_2(v_inst_1647_, lean_box(0), v___x_1661_);
lean_inc(v___x_1662_);
lean_inc_n(v_toBind_1645_, 2);
v___f_1663_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1663_, 0, v_toPure_1644_);
lean_closure_set(v___f_1663_, 1, v_toBind_1645_);
lean_closure_set(v___f_1663_, 2, v___x_1662_);
lean_closure_set(v___f_1663_, 3, v___x_1656_);
v___x_1664_ = lean_apply_4(v_toBind_1645_, lean_box(0), lean_box(0), v___x_1662_, v___f_1663_);
v___x_1665_ = lean_apply_4(v_toBind_1645_, lean_box(0), lean_box(0), v___x_1664_, v___f_1652_);
return v___x_1665_;
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___f_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1666_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1667_ = lean_apply_2(v_inst_1647_, lean_box(0), v___x_1666_);
lean_inc(v___x_1667_);
lean_inc_n(v_toBind_1645_, 2);
v___f_1668_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_1668_, 0, v_toPure_1644_);
lean_closure_set(v___f_1668_, 1, v_toBind_1645_);
lean_closure_set(v___f_1668_, 2, v___x_1667_);
lean_closure_set(v___f_1668_, 3, v___x_1656_);
v___x_1669_ = lean_apply_4(v_toBind_1645_, lean_box(0), lean_box(0), v___x_1667_, v___f_1668_);
v___x_1670_ = lean_apply_4(v_toBind_1645_, lean_box(0), lean_box(0), v___x_1669_, v___f_1652_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_always_1671_ = _args[0];
lean_object* v_inst_1672_ = _args[1];
lean_object* v_inst_1673_ = _args[2];
lean_object* v_inst_1674_ = _args[3];
lean_object* v_inst_1675_ = _args[4];
lean_object* v_inst_1676_ = _args[5];
lean_object* v_cls_1677_ = _args[6];
lean_object* v_collapsed_1678_ = _args[7];
lean_object* v_tag_1679_ = _args[8];
lean_object* v_opts_1680_ = _args[9];
lean_object* v_clsEnabled_1681_ = _args[10];
lean_object* v_msg_1682_ = _args[11];
lean_object* v_toPure_1683_ = _args[12];
lean_object* v_toBind_1684_ = _args[13];
lean_object* v_k_1685_ = _args[14];
lean_object* v_inst_1686_ = _args[15];
lean_object* v_oldTraces_1687_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1688_; uint8_t v_clsEnabled_boxed_1689_; lean_object* v_res_1690_; 
v_collapsed_boxed_1688_ = lean_unbox(v_collapsed_1678_);
v_clsEnabled_boxed_1689_ = lean_unbox(v_clsEnabled_1681_);
v_res_1690_ = l_Lean_withTraceNode___redArg___lam__9(v_always_1671_, v_inst_1672_, v_inst_1673_, v_inst_1674_, v_inst_1675_, v_inst_1676_, v_cls_1677_, v_collapsed_boxed_1688_, v_tag_1679_, v_opts_1680_, v_clsEnabled_boxed_1689_, v_msg_1682_, v_toPure_1683_, v_toBind_1684_, v_k_1685_, v_inst_1686_, v_oldTraces_1687_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object* v_always_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_cls_1697_, uint8_t v_collapsed_1698_, lean_object* v_tag_1699_, lean_object* v_opts_1700_, lean_object* v_msg_1701_, lean_object* v_toPure_1702_, lean_object* v_toBind_1703_, lean_object* v_k_1704_, lean_object* v_inst_1705_, uint8_t v_clsEnabled_1706_){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___f_1709_; 
v___x_1707_ = lean_box(v_collapsed_1698_);
v___x_1708_ = lean_box(v_clsEnabled_1706_);
lean_inc(v_k_1704_);
lean_inc(v_toBind_1703_);
lean_inc_ref(v_opts_1700_);
lean_inc_ref(v_inst_1693_);
lean_inc_ref(v_inst_1692_);
v___f_1709_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_1709_, 0, v_always_1691_);
lean_closure_set(v___f_1709_, 1, v_inst_1692_);
lean_closure_set(v___f_1709_, 2, v_inst_1693_);
lean_closure_set(v___f_1709_, 3, v_inst_1694_);
lean_closure_set(v___f_1709_, 4, v_inst_1695_);
lean_closure_set(v___f_1709_, 5, v_inst_1696_);
lean_closure_set(v___f_1709_, 6, v_cls_1697_);
lean_closure_set(v___f_1709_, 7, v___x_1707_);
lean_closure_set(v___f_1709_, 8, v_tag_1699_);
lean_closure_set(v___f_1709_, 9, v_opts_1700_);
lean_closure_set(v___f_1709_, 10, v___x_1708_);
lean_closure_set(v___f_1709_, 11, v_msg_1701_);
lean_closure_set(v___f_1709_, 12, v_toPure_1702_);
lean_closure_set(v___f_1709_, 13, v_toBind_1703_);
lean_closure_set(v___f_1709_, 14, v_k_1704_);
lean_closure_set(v___f_1709_, 15, v_inst_1705_);
if (v_clsEnabled_1706_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1713_ = l_Lean_KVMap_instValueBool;
v___x_1714_ = l_Lean_trace_profiler;
v___x_1715_ = l_Lean_Option_get___redArg(v___x_1713_, v_opts_1700_, v___x_1714_);
lean_dec_ref(v_opts_1700_);
v___x_1716_ = lean_unbox(v___x_1715_);
lean_dec(v___x_1715_);
if (v___x_1716_ == 0)
{
lean_dec_ref(v___f_1709_);
lean_dec(v_toBind_1703_);
lean_dec_ref(v_inst_1693_);
lean_dec_ref(v_inst_1692_);
return v_k_1704_;
}
else
{
lean_dec(v_k_1704_);
goto v___jp_1710_;
}
}
else
{
lean_dec(v_k_1704_);
lean_dec_ref(v_opts_1700_);
goto v___jp_1710_;
}
v___jp_1710_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1692_, v_inst_1693_);
v___x_1712_ = lean_apply_4(v_toBind_1703_, lean_box(0), lean_box(0), v___x_1711_, v___f_1709_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object* v_always_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_inst_1722_, lean_object* v_cls_1723_, lean_object* v_collapsed_1724_, lean_object* v_tag_1725_, lean_object* v_opts_1726_, lean_object* v_msg_1727_, lean_object* v_toPure_1728_, lean_object* v_toBind_1729_, lean_object* v_k_1730_, lean_object* v_inst_1731_, lean_object* v_clsEnabled_1732_){
_start:
{
uint8_t v_collapsed_boxed_1733_; uint8_t v_clsEnabled_boxed_1734_; lean_object* v_res_1735_; 
v_collapsed_boxed_1733_ = lean_unbox(v_collapsed_1724_);
v_clsEnabled_boxed_1734_ = lean_unbox(v_clsEnabled_1732_);
v_res_1735_ = l_Lean_withTraceNode___redArg___lam__10(v_always_1717_, v_inst_1718_, v_inst_1719_, v_inst_1720_, v_inst_1721_, v_inst_1722_, v_cls_1723_, v_collapsed_boxed_1733_, v_tag_1725_, v_opts_1726_, v_msg_1727_, v_toPure_1728_, v_toBind_1729_, v_k_1730_, v_inst_1731_, v_clsEnabled_boxed_1734_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object* v_k_1736_, lean_object* v_inst_1737_, lean_object* v_toApplicative_1738_, lean_object* v_always_1739_, lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_cls_1744_, uint8_t v_collapsed_1745_, lean_object* v_tag_1746_, lean_object* v_msg_1747_, lean_object* v_toBind_1748_, lean_object* v_inst_1749_, lean_object* v_inst_1750_, lean_object* v_opts_1751_){
_start:
{
uint8_t v_hasTrace_1752_; 
v_hasTrace_1752_ = lean_ctor_get_uint8(v_opts_1751_, sizeof(void*)*1);
if (v_hasTrace_1752_ == 0)
{
lean_dec_ref(v_opts_1751_);
lean_dec(v_inst_1750_);
lean_dec(v_inst_1749_);
lean_dec(v_toBind_1748_);
lean_dec(v_msg_1747_);
lean_dec_ref(v_tag_1746_);
lean_dec(v_cls_1744_);
lean_dec_ref(v_inst_1743_);
lean_dec(v_inst_1742_);
lean_dec_ref(v_inst_1741_);
lean_dec_ref(v_inst_1740_);
lean_dec_ref(v_always_1739_);
lean_dec_ref(v_toApplicative_1738_);
lean_dec_ref(v_inst_1737_);
return v_k_1736_;
}
else
{
lean_object* v_getInheritedTraceOptions_1753_; lean_object* v_toPure_1754_; lean_object* v___x_1755_; lean_object* v___f_1756_; lean_object* v___f_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v_getInheritedTraceOptions_1753_ = lean_ctor_get(v_inst_1737_, 2);
lean_inc(v_getInheritedTraceOptions_1753_);
v_toPure_1754_ = lean_ctor_get(v_toApplicative_1738_, 1);
lean_inc_n(v_toPure_1754_, 2);
lean_dec_ref(v_toApplicative_1738_);
v___x_1755_ = lean_box(v_collapsed_1745_);
lean_inc_n(v_toBind_1748_, 3);
lean_inc(v_cls_1744_);
v___f_1756_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_1756_, 0, v_always_1739_);
lean_closure_set(v___f_1756_, 1, v_inst_1740_);
lean_closure_set(v___f_1756_, 2, v_inst_1737_);
lean_closure_set(v___f_1756_, 3, v_inst_1741_);
lean_closure_set(v___f_1756_, 4, v_inst_1742_);
lean_closure_set(v___f_1756_, 5, v_inst_1743_);
lean_closure_set(v___f_1756_, 6, v_cls_1744_);
lean_closure_set(v___f_1756_, 7, v___x_1755_);
lean_closure_set(v___f_1756_, 8, v_tag_1746_);
lean_closure_set(v___f_1756_, 9, v_opts_1751_);
lean_closure_set(v___f_1756_, 10, v_msg_1747_);
lean_closure_set(v___f_1756_, 11, v_toPure_1754_);
lean_closure_set(v___f_1756_, 12, v_toBind_1748_);
lean_closure_set(v___f_1756_, 13, v_k_1736_);
lean_closure_set(v___f_1756_, 14, v_inst_1749_);
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1757_, 0, v_toPure_1754_);
lean_closure_set(v___f_1757_, 1, v_cls_1744_);
lean_closure_set(v___f_1757_, 2, v_toBind_1748_);
lean_closure_set(v___f_1757_, 3, v_inst_1750_);
v___x_1758_ = lean_apply_4(v_toBind_1748_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1753_, v___f_1757_);
v___x_1759_ = lean_apply_4(v_toBind_1748_, lean_box(0), lean_box(0), v___x_1758_, v___f_1756_);
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13___boxed(lean_object* v_k_1760_, lean_object* v_inst_1761_, lean_object* v_toApplicative_1762_, lean_object* v_always_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_cls_1768_, lean_object* v_collapsed_1769_, lean_object* v_tag_1770_, lean_object* v_msg_1771_, lean_object* v_toBind_1772_, lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_opts_1775_){
_start:
{
uint8_t v_collapsed_boxed_1776_; lean_object* v_res_1777_; 
v_collapsed_boxed_1776_ = lean_unbox(v_collapsed_1769_);
v_res_1777_ = l_Lean_withTraceNode___redArg___lam__13(v_k_1760_, v_inst_1761_, v_toApplicative_1762_, v_always_1763_, v_inst_1764_, v_inst_1765_, v_inst_1766_, v_inst_1767_, v_cls_1768_, v_collapsed_boxed_1776_, v_tag_1770_, v_msg_1771_, v_toBind_1772_, v_inst_1773_, v_inst_1774_, v_opts_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_always_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_cls_1786_, lean_object* v_msg_1787_, lean_object* v_k_1788_, uint8_t v_collapsed_1789_, lean_object* v_tag_1790_){
_start:
{
lean_object* v_toApplicative_1791_; lean_object* v_toBind_1792_; lean_object* v___x_1793_; lean_object* v___f_1794_; lean_object* v___x_1795_; 
v_toApplicative_1791_ = lean_ctor_get(v_inst_1778_, 0);
lean_inc_ref(v_toApplicative_1791_);
v_toBind_1792_ = lean_ctor_get(v_inst_1778_, 1);
lean_inc_n(v_toBind_1792_, 2);
v___x_1793_ = lean_box(v_collapsed_1789_);
lean_inc(v_inst_1782_);
v___f_1794_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1794_, 0, v_k_1788_);
lean_closure_set(v___f_1794_, 1, v_inst_1779_);
lean_closure_set(v___f_1794_, 2, v_toApplicative_1791_);
lean_closure_set(v___f_1794_, 3, v_always_1783_);
lean_closure_set(v___f_1794_, 4, v_inst_1778_);
lean_closure_set(v___f_1794_, 5, v_inst_1780_);
lean_closure_set(v___f_1794_, 6, v_inst_1781_);
lean_closure_set(v___f_1794_, 7, v_inst_1785_);
lean_closure_set(v___f_1794_, 8, v_cls_1786_);
lean_closure_set(v___f_1794_, 9, v___x_1793_);
lean_closure_set(v___f_1794_, 10, v_tag_1790_);
lean_closure_set(v___f_1794_, 11, v_msg_1787_);
lean_closure_set(v___f_1794_, 12, v_toBind_1792_);
lean_closure_set(v___f_1794_, 13, v_inst_1784_);
lean_closure_set(v___f_1794_, 14, v_inst_1782_);
v___x_1795_ = lean_apply_4(v_toBind_1792_, lean_box(0), lean_box(0), v_inst_1782_, v___f_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_, lean_object* v_inst_1799_, lean_object* v_inst_1800_, lean_object* v_always_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_cls_1804_, lean_object* v_msg_1805_, lean_object* v_k_1806_, lean_object* v_collapsed_1807_, lean_object* v_tag_1808_){
_start:
{
uint8_t v_collapsed_boxed_1809_; lean_object* v_res_1810_; 
v_collapsed_boxed_1809_ = lean_unbox(v_collapsed_1807_);
v_res_1810_ = l_Lean_withTraceNode___redArg(v_inst_1796_, v_inst_1797_, v_inst_1798_, v_inst_1799_, v_inst_1800_, v_always_1801_, v_inst_1802_, v_inst_1803_, v_cls_1804_, v_msg_1805_, v_k_1806_, v_collapsed_boxed_1809_, v_tag_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object* v_00_u03b1_1811_, lean_object* v_m_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_00_u03b5_1818_, lean_object* v_always_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_cls_1822_, lean_object* v_msg_1823_, lean_object* v_k_1824_, uint8_t v_collapsed_1825_, lean_object* v_tag_1826_){
_start:
{
lean_object* v_toApplicative_1827_; lean_object* v_toBind_1828_; lean_object* v___x_1829_; lean_object* v___f_1830_; lean_object* v___x_1831_; 
v_toApplicative_1827_ = lean_ctor_get(v_inst_1813_, 0);
lean_inc_ref(v_toApplicative_1827_);
v_toBind_1828_ = lean_ctor_get(v_inst_1813_, 1);
lean_inc_n(v_toBind_1828_, 2);
v___x_1829_ = lean_box(v_collapsed_1825_);
lean_inc(v_inst_1817_);
v___f_1830_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1830_, 0, v_k_1824_);
lean_closure_set(v___f_1830_, 1, v_inst_1814_);
lean_closure_set(v___f_1830_, 2, v_toApplicative_1827_);
lean_closure_set(v___f_1830_, 3, v_always_1819_);
lean_closure_set(v___f_1830_, 4, v_inst_1813_);
lean_closure_set(v___f_1830_, 5, v_inst_1815_);
lean_closure_set(v___f_1830_, 6, v_inst_1816_);
lean_closure_set(v___f_1830_, 7, v_inst_1821_);
lean_closure_set(v___f_1830_, 8, v_cls_1822_);
lean_closure_set(v___f_1830_, 9, v___x_1829_);
lean_closure_set(v___f_1830_, 10, v_tag_1826_);
lean_closure_set(v___f_1830_, 11, v_msg_1823_);
lean_closure_set(v___f_1830_, 12, v_toBind_1828_);
lean_closure_set(v___f_1830_, 13, v_inst_1820_);
lean_closure_set(v___f_1830_, 14, v_inst_1817_);
v___x_1831_ = lean_apply_4(v_toBind_1828_, lean_box(0), lean_box(0), v_inst_1817_, v___f_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object* v_00_u03b1_1832_, lean_object* v_m_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_, lean_object* v_00_u03b5_1839_, lean_object* v_always_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_cls_1843_, lean_object* v_msg_1844_, lean_object* v_k_1845_, lean_object* v_collapsed_1846_, lean_object* v_tag_1847_){
_start:
{
uint8_t v_collapsed_boxed_1848_; lean_object* v_res_1849_; 
v_collapsed_boxed_1848_ = lean_unbox(v_collapsed_1846_);
v_res_1849_ = l_Lean_withTraceNode(v_00_u03b1_1832_, v_m_1833_, v_inst_1834_, v_inst_1835_, v_inst_1836_, v_inst_1837_, v_inst_1838_, v_00_u03b5_1839_, v_always_1840_, v_inst_1841_, v_inst_1842_, v_cls_1843_, v_msg_1844_, v_k_1845_, v_collapsed_boxed_1848_, v_tag_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object* v_self_1850_){
_start:
{
lean_object* v_fst_1851_; 
v_fst_1851_ = lean_ctor_get(v_self_1850_, 0);
lean_inc(v_fst_1851_);
return v_fst_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object* v_self_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_1852_);
lean_dec_ref(v_self_1852_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object* v_toPure_1854_, lean_object* v_x_1855_){
_start:
{
if (lean_obj_tag(v_x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v_a_1856_ = lean_ctor_get(v_x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref(v_x_1855_);
v___x_1857_ = l_Lean_Exception_toMessageData(v_a_1856_);
v___x_1858_ = lean_apply_2(v_toPure_1854_, lean_box(0), v___x_1857_);
return v___x_1858_;
}
else
{
lean_object* v_a_1859_; lean_object* v_snd_1860_; lean_object* v___x_1861_; 
v_a_1859_ = lean_ctor_get(v_x_1855_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v_x_1855_);
v_snd_1860_ = lean_ctor_get(v_a_1859_, 1);
lean_inc(v_snd_1860_);
lean_dec(v_a_1859_);
v___x_1861_ = lean_apply_2(v_toPure_1854_, lean_box(0), v_snd_1860_);
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object* v_toPure_1862_, lean_object* v_ex_1863_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_ex_1863_);
v___x_1865_ = lean_apply_2(v_toPure_1862_, lean_box(0), v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object* v_toPure_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_a_1867_);
v___x_1869_ = lean_apply_2(v_toPure_1866_, lean_box(0), v___x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v___f_1875_, lean_object* v_cls_1876_, uint8_t v_collapsed_1877_, lean_object* v_tag_1878_, lean_object* v_opts_1879_, uint8_t v_clsEnabled_1880_, lean_object* v_oldTraces_1881_, lean_object* v_msg_1882_, lean_object* v_resStartStop_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1870_, v_inst_1871_, v_inst_1872_, v_inst_1873_, v_inst_1874_, v___f_1875_, v_cls_1876_, v_collapsed_1877_, v_tag_1878_, v_opts_1879_, v_clsEnabled_1880_, v_oldTraces_1881_, v_msg_1882_, v_resStartStop_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3___boxed(lean_object* v_inst_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v___f_1890_, lean_object* v_cls_1891_, lean_object* v_collapsed_1892_, lean_object* v_tag_1893_, lean_object* v_opts_1894_, lean_object* v_clsEnabled_1895_, lean_object* v_oldTraces_1896_, lean_object* v_msg_1897_, lean_object* v_resStartStop_1898_){
_start:
{
uint8_t v_collapsed_boxed_1899_; uint8_t v_clsEnabled_boxed_1900_; lean_object* v_res_1901_; 
v_collapsed_boxed_1899_ = lean_unbox(v_collapsed_1892_);
v_clsEnabled_boxed_1900_ = lean_unbox(v_clsEnabled_1895_);
v_res_1901_ = l_Lean_withTraceNode_x27___redArg___lam__3(v_inst_1885_, v_inst_1886_, v_inst_1887_, v_inst_1888_, v_inst_1889_, v___f_1890_, v_cls_1891_, v_collapsed_boxed_1899_, v_tag_1893_, v_opts_1894_, v_clsEnabled_boxed_1900_, v_oldTraces_1896_, v_msg_1897_, v_resStartStop_1898_);
lean_dec_ref(v_opts_1894_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object* v_start_1902_, lean_object* v_a_1903_, lean_object* v_toPure_1904_, lean_object* v_stop_1905_){
_start:
{
double v___x_1906_; double v___x_1907_; double v___x_1908_; double v___x_1909_; double v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1906_ = lean_float_of_nat(v_start_1902_);
v___x_1907_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1908_ = lean_float_div(v___x_1906_, v___x_1907_);
v___x_1909_ = lean_float_of_nat(v_stop_1905_);
v___x_1910_ = lean_float_div(v___x_1909_, v___x_1907_);
v___x_1911_ = lean_box_float(v___x_1908_);
v___x_1912_ = lean_box_float(v___x_1910_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v_a_1903_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_apply_2(v_toPure_1904_, lean_box(0), v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object* v_start_1916_, lean_object* v_toPure_1917_, lean_object* v_toBind_1918_, lean_object* v___x_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v___f_1921_; lean_object* v___x_1922_; 
v___f_1921_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__5), 4, 3);
lean_closure_set(v___f_1921_, 0, v_start_1916_);
lean_closure_set(v___f_1921_, 1, v_a_1920_);
lean_closure_set(v___f_1921_, 2, v_toPure_1917_);
v___x_1922_ = lean_apply_4(v_toBind_1918_, lean_box(0), lean_box(0), v___x_1919_, v___f_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object* v_toPure_1923_, lean_object* v_toBind_1924_, lean_object* v___x_1925_, lean_object* v___x_1926_, lean_object* v_start_1927_){
_start:
{
lean_object* v___f_1928_; lean_object* v___x_1929_; 
lean_inc(v_toBind_1924_);
v___f_1928_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__6), 5, 4);
lean_closure_set(v___f_1928_, 0, v_start_1927_);
lean_closure_set(v___f_1928_, 1, v_toPure_1923_);
lean_closure_set(v___f_1928_, 2, v_toBind_1924_);
lean_closure_set(v___f_1928_, 3, v___x_1925_);
v___x_1929_ = lean_apply_4(v_toBind_1924_, lean_box(0), lean_box(0), v___x_1926_, v___f_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object* v_start_1930_, lean_object* v_a_1931_, lean_object* v_toPure_1932_, lean_object* v_stop_1933_){
_start:
{
double v___x_1934_; double v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1934_ = lean_float_of_nat(v_start_1930_);
v___x_1935_ = lean_float_of_nat(v_stop_1933_);
v___x_1936_ = lean_box_float(v___x_1934_);
v___x_1937_ = lean_box_float(v___x_1935_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v_a_1931_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = lean_apply_2(v_toPure_1932_, lean_box(0), v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object* v_start_1941_, lean_object* v_toPure_1942_, lean_object* v_toBind_1943_, lean_object* v___x_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___f_1946_; lean_object* v___x_1947_; 
v___f_1946_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__8), 4, 3);
lean_closure_set(v___f_1946_, 0, v_start_1941_);
lean_closure_set(v___f_1946_, 1, v_a_1945_);
lean_closure_set(v___f_1946_, 2, v_toPure_1942_);
v___x_1947_ = lean_apply_4(v_toBind_1943_, lean_box(0), lean_box(0), v___x_1944_, v___f_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object* v_toPure_1948_, lean_object* v_toBind_1949_, lean_object* v___x_1950_, lean_object* v___x_1951_, lean_object* v_start_1952_){
_start:
{
lean_object* v___f_1953_; lean_object* v___x_1954_; 
lean_inc(v_toBind_1949_);
v___f_1953_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__9), 5, 4);
lean_closure_set(v___f_1953_, 0, v_start_1952_);
lean_closure_set(v___f_1953_, 1, v_toPure_1948_);
lean_closure_set(v___f_1953_, 2, v_toBind_1949_);
lean_closure_set(v___f_1953_, 3, v___x_1950_);
v___x_1954_ = lean_apply_4(v_toBind_1949_, lean_box(0), lean_box(0), v___x_1951_, v___f_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v___f_1960_, lean_object* v_cls_1961_, uint8_t v_collapsed_1962_, lean_object* v_tag_1963_, lean_object* v_opts_1964_, uint8_t v_clsEnabled_1965_, lean_object* v_msg_1966_, lean_object* v_toBind_1967_, lean_object* v_k_1968_, lean_object* v___f_1969_, lean_object* v___f_1970_, lean_object* v_inst_1971_, lean_object* v_toPure_1972_, lean_object* v_oldTraces_1973_){
_start:
{
lean_object* v_tryCatch_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___f_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v_tryCatch_1974_ = lean_ctor_get(v_inst_1955_, 1);
lean_inc(v_tryCatch_1974_);
v___x_1975_ = lean_box(v_collapsed_1962_);
v___x_1976_ = lean_box(v_clsEnabled_1965_);
lean_inc_ref(v_opts_1964_);
v___f_1977_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_1977_, 0, v_inst_1956_);
lean_closure_set(v___f_1977_, 1, v_inst_1957_);
lean_closure_set(v___f_1977_, 2, v_inst_1958_);
lean_closure_set(v___f_1977_, 3, v_inst_1959_);
lean_closure_set(v___f_1977_, 4, v_inst_1955_);
lean_closure_set(v___f_1977_, 5, v___f_1960_);
lean_closure_set(v___f_1977_, 6, v_cls_1961_);
lean_closure_set(v___f_1977_, 7, v___x_1975_);
lean_closure_set(v___f_1977_, 8, v_tag_1963_);
lean_closure_set(v___f_1977_, 9, v_opts_1964_);
lean_closure_set(v___f_1977_, 10, v___x_1976_);
lean_closure_set(v___f_1977_, 11, v_oldTraces_1973_);
lean_closure_set(v___f_1977_, 12, v_msg_1966_);
lean_inc(v_toBind_1967_);
v___x_1978_ = lean_apply_4(v_toBind_1967_, lean_box(0), lean_box(0), v_k_1968_, v___f_1969_);
v___x_1979_ = lean_apply_3(v_tryCatch_1974_, lean_box(0), v___x_1978_, v___f_1970_);
v___x_1980_ = l_Lean_KVMap_instValueBool;
v___x_1981_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1982_ = l_Lean_Option_get___redArg(v___x_1980_, v_opts_1964_, v___x_1981_);
lean_dec_ref(v_opts_1964_);
v___x_1983_ = lean_unbox(v___x_1982_);
lean_dec(v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___f_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1984_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1985_ = lean_apply_2(v_inst_1971_, lean_box(0), v___x_1984_);
lean_inc(v___x_1985_);
lean_inc_n(v_toBind_1967_, 2);
v___f_1986_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1986_, 0, v_toPure_1972_);
lean_closure_set(v___f_1986_, 1, v_toBind_1967_);
lean_closure_set(v___f_1986_, 2, v___x_1985_);
lean_closure_set(v___f_1986_, 3, v___x_1979_);
v___x_1987_ = lean_apply_4(v_toBind_1967_, lean_box(0), lean_box(0), v___x_1985_, v___f_1986_);
v___x_1988_ = lean_apply_4(v_toBind_1967_, lean_box(0), lean_box(0), v___x_1987_, v___f_1977_);
return v___x_1988_;
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___f_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1989_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1990_ = lean_apply_2(v_inst_1971_, lean_box(0), v___x_1989_);
lean_inc(v___x_1990_);
lean_inc_n(v_toBind_1967_, 2);
v___f_1991_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__10), 5, 4);
lean_closure_set(v___f_1991_, 0, v_toPure_1972_);
lean_closure_set(v___f_1991_, 1, v_toBind_1967_);
lean_closure_set(v___f_1991_, 2, v___x_1990_);
lean_closure_set(v___f_1991_, 3, v___x_1979_);
v___x_1992_ = lean_apply_4(v_toBind_1967_, lean_box(0), lean_box(0), v___x_1990_, v___f_1991_);
v___x_1993_ = lean_apply_4(v_toBind_1967_, lean_box(0), lean_box(0), v___x_1992_, v___f_1977_);
return v___x_1993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_1994_ = _args[0];
lean_object* v_inst_1995_ = _args[1];
lean_object* v_inst_1996_ = _args[2];
lean_object* v_inst_1997_ = _args[3];
lean_object* v_inst_1998_ = _args[4];
lean_object* v___f_1999_ = _args[5];
lean_object* v_cls_2000_ = _args[6];
lean_object* v_collapsed_2001_ = _args[7];
lean_object* v_tag_2002_ = _args[8];
lean_object* v_opts_2003_ = _args[9];
lean_object* v_clsEnabled_2004_ = _args[10];
lean_object* v_msg_2005_ = _args[11];
lean_object* v_toBind_2006_ = _args[12];
lean_object* v_k_2007_ = _args[13];
lean_object* v___f_2008_ = _args[14];
lean_object* v___f_2009_ = _args[15];
lean_object* v_inst_2010_ = _args[16];
lean_object* v_toPure_2011_ = _args[17];
lean_object* v_oldTraces_2012_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_2013_; uint8_t v_clsEnabled_boxed_2014_; lean_object* v_res_2015_; 
v_collapsed_boxed_2013_ = lean_unbox(v_collapsed_2001_);
v_clsEnabled_boxed_2014_ = lean_unbox(v_clsEnabled_2004_);
v_res_2015_ = l_Lean_withTraceNode_x27___redArg___lam__11(v_inst_1994_, v_inst_1995_, v_inst_1996_, v_inst_1997_, v_inst_1998_, v___f_1999_, v_cls_2000_, v_collapsed_boxed_2013_, v_tag_2002_, v_opts_2003_, v_clsEnabled_boxed_2014_, v_msg_2005_, v_toBind_2006_, v_k_2007_, v___f_2008_, v___f_2009_, v_inst_2010_, v_toPure_2011_, v_oldTraces_2012_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_inst_2020_, lean_object* v___f_2021_, lean_object* v_cls_2022_, uint8_t v_collapsed_2023_, lean_object* v_tag_2024_, lean_object* v_opts_2025_, lean_object* v_msg_2026_, lean_object* v_toBind_2027_, lean_object* v_k_2028_, lean_object* v___f_2029_, lean_object* v___f_2030_, lean_object* v_inst_2031_, lean_object* v_toPure_2032_, uint8_t v_clsEnabled_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___f_2036_; 
v___x_2034_ = lean_box(v_collapsed_2023_);
v___x_2035_ = lean_box(v_clsEnabled_2033_);
lean_inc(v_k_2028_);
lean_inc(v_toBind_2027_);
lean_inc_ref(v_opts_2025_);
lean_inc_ref(v_inst_2018_);
lean_inc_ref(v_inst_2017_);
v___f_2036_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__11___boxed), 19, 18);
lean_closure_set(v___f_2036_, 0, v_inst_2016_);
lean_closure_set(v___f_2036_, 1, v_inst_2017_);
lean_closure_set(v___f_2036_, 2, v_inst_2018_);
lean_closure_set(v___f_2036_, 3, v_inst_2019_);
lean_closure_set(v___f_2036_, 4, v_inst_2020_);
lean_closure_set(v___f_2036_, 5, v___f_2021_);
lean_closure_set(v___f_2036_, 6, v_cls_2022_);
lean_closure_set(v___f_2036_, 7, v___x_2034_);
lean_closure_set(v___f_2036_, 8, v_tag_2024_);
lean_closure_set(v___f_2036_, 9, v_opts_2025_);
lean_closure_set(v___f_2036_, 10, v___x_2035_);
lean_closure_set(v___f_2036_, 11, v_msg_2026_);
lean_closure_set(v___f_2036_, 12, v_toBind_2027_);
lean_closure_set(v___f_2036_, 13, v_k_2028_);
lean_closure_set(v___f_2036_, 14, v___f_2029_);
lean_closure_set(v___f_2036_, 15, v___f_2030_);
lean_closure_set(v___f_2036_, 16, v_inst_2031_);
lean_closure_set(v___f_2036_, 17, v_toPure_2032_);
if (v_clsEnabled_2033_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2040_ = l_Lean_KVMap_instValueBool;
v___x_2041_ = l_Lean_trace_profiler;
v___x_2042_ = l_Lean_Option_get___redArg(v___x_2040_, v_opts_2025_, v___x_2041_);
lean_dec_ref(v_opts_2025_);
v___x_2043_ = lean_unbox(v___x_2042_);
lean_dec(v___x_2042_);
if (v___x_2043_ == 0)
{
lean_dec_ref(v___f_2036_);
lean_dec(v_toBind_2027_);
lean_dec_ref(v_inst_2018_);
lean_dec_ref(v_inst_2017_);
return v_k_2028_;
}
else
{
lean_dec(v_k_2028_);
goto v___jp_2037_;
}
}
else
{
lean_dec(v_k_2028_);
lean_dec_ref(v_opts_2025_);
goto v___jp_2037_;
}
v___jp_2037_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_2017_, v_inst_2018_);
v___x_2039_ = lean_apply_4(v_toBind_2027_, lean_box(0), lean_box(0), v___x_2038_, v___f_2036_);
return v___x_2039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_inst_2044_ = _args[0];
lean_object* v_inst_2045_ = _args[1];
lean_object* v_inst_2046_ = _args[2];
lean_object* v_inst_2047_ = _args[3];
lean_object* v_inst_2048_ = _args[4];
lean_object* v___f_2049_ = _args[5];
lean_object* v_cls_2050_ = _args[6];
lean_object* v_collapsed_2051_ = _args[7];
lean_object* v_tag_2052_ = _args[8];
lean_object* v_opts_2053_ = _args[9];
lean_object* v_msg_2054_ = _args[10];
lean_object* v_toBind_2055_ = _args[11];
lean_object* v_k_2056_ = _args[12];
lean_object* v___f_2057_ = _args[13];
lean_object* v___f_2058_ = _args[14];
lean_object* v_inst_2059_ = _args[15];
lean_object* v_toPure_2060_ = _args[16];
lean_object* v_clsEnabled_2061_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2062_; uint8_t v_clsEnabled_boxed_2063_; lean_object* v_res_2064_; 
v_collapsed_boxed_2062_ = lean_unbox(v_collapsed_2051_);
v_clsEnabled_boxed_2063_ = lean_unbox(v_clsEnabled_2061_);
v_res_2064_ = l_Lean_withTraceNode_x27___redArg___lam__12(v_inst_2044_, v_inst_2045_, v_inst_2046_, v_inst_2047_, v_inst_2048_, v___f_2049_, v_cls_2050_, v_collapsed_boxed_2062_, v_tag_2052_, v_opts_2053_, v_msg_2054_, v_toBind_2055_, v_k_2056_, v___f_2057_, v___f_2058_, v_inst_2059_, v_toPure_2060_, v_clsEnabled_boxed_2063_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object* v_k_2065_, lean_object* v_inst_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v___f_2071_, lean_object* v_cls_2072_, uint8_t v_collapsed_2073_, lean_object* v_tag_2074_, lean_object* v_msg_2075_, lean_object* v_toBind_2076_, lean_object* v___f_2077_, lean_object* v___f_2078_, lean_object* v_inst_2079_, lean_object* v_toPure_2080_, lean_object* v___f_2081_, lean_object* v_opts_2082_){
_start:
{
uint8_t v_hasTrace_2083_; 
v_hasTrace_2083_ = lean_ctor_get_uint8(v_opts_2082_, sizeof(void*)*1);
if (v_hasTrace_2083_ == 0)
{
lean_dec_ref(v_opts_2082_);
lean_dec(v___f_2081_);
lean_dec(v_toPure_2080_);
lean_dec(v_inst_2079_);
lean_dec(v___f_2078_);
lean_dec(v___f_2077_);
lean_dec(v_toBind_2076_);
lean_dec(v_msg_2075_);
lean_dec_ref(v_tag_2074_);
lean_dec(v_cls_2072_);
lean_dec_ref(v___f_2071_);
lean_dec(v_inst_2070_);
lean_dec_ref(v_inst_2069_);
lean_dec_ref(v_inst_2068_);
lean_dec_ref(v_inst_2067_);
lean_dec_ref(v_inst_2066_);
return v_k_2065_;
}
else
{
lean_object* v_getInheritedTraceOptions_2084_; lean_object* v___x_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_getInheritedTraceOptions_2084_ = lean_ctor_get(v_inst_2066_, 2);
lean_inc(v_getInheritedTraceOptions_2084_);
v___x_2085_ = lean_box(v_collapsed_2073_);
lean_inc_n(v_toBind_2076_, 2);
v___f_2086_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_2086_, 0, v_inst_2067_);
lean_closure_set(v___f_2086_, 1, v_inst_2068_);
lean_closure_set(v___f_2086_, 2, v_inst_2066_);
lean_closure_set(v___f_2086_, 3, v_inst_2069_);
lean_closure_set(v___f_2086_, 4, v_inst_2070_);
lean_closure_set(v___f_2086_, 5, v___f_2071_);
lean_closure_set(v___f_2086_, 6, v_cls_2072_);
lean_closure_set(v___f_2086_, 7, v___x_2085_);
lean_closure_set(v___f_2086_, 8, v_tag_2074_);
lean_closure_set(v___f_2086_, 9, v_opts_2082_);
lean_closure_set(v___f_2086_, 10, v_msg_2075_);
lean_closure_set(v___f_2086_, 11, v_toBind_2076_);
lean_closure_set(v___f_2086_, 12, v_k_2065_);
lean_closure_set(v___f_2086_, 13, v___f_2077_);
lean_closure_set(v___f_2086_, 14, v___f_2078_);
lean_closure_set(v___f_2086_, 15, v_inst_2079_);
lean_closure_set(v___f_2086_, 16, v_toPure_2080_);
v___x_2087_ = lean_apply_4(v_toBind_2076_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2084_, v___f_2081_);
v___x_2088_ = lean_apply_4(v_toBind_2076_, lean_box(0), lean_box(0), v___x_2087_, v___f_2086_);
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_k_2089_ = _args[0];
lean_object* v_inst_2090_ = _args[1];
lean_object* v_inst_2091_ = _args[2];
lean_object* v_inst_2092_ = _args[3];
lean_object* v_inst_2093_ = _args[4];
lean_object* v_inst_2094_ = _args[5];
lean_object* v___f_2095_ = _args[6];
lean_object* v_cls_2096_ = _args[7];
lean_object* v_collapsed_2097_ = _args[8];
lean_object* v_tag_2098_ = _args[9];
lean_object* v_msg_2099_ = _args[10];
lean_object* v_toBind_2100_ = _args[11];
lean_object* v___f_2101_ = _args[12];
lean_object* v___f_2102_ = _args[13];
lean_object* v_inst_2103_ = _args[14];
lean_object* v_toPure_2104_ = _args[15];
lean_object* v___f_2105_ = _args[16];
lean_object* v_opts_2106_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2107_; lean_object* v_res_2108_; 
v_collapsed_boxed_2107_ = lean_unbox(v_collapsed_2097_);
v_res_2108_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_k_2089_, v_inst_2090_, v_inst_2091_, v_inst_2092_, v_inst_2093_, v_inst_2094_, v___f_2095_, v_cls_2096_, v_collapsed_boxed_2107_, v_tag_2098_, v_msg_2099_, v_toBind_2100_, v___f_2101_, v___f_2102_, v_inst_2103_, v_toPure_2104_, v___f_2105_, v_opts_2106_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_cls_2117_, lean_object* v_k_2118_, uint8_t v_collapsed_2119_, lean_object* v_tag_2120_){
_start:
{
lean_object* v_toApplicative_2121_; lean_object* v_toFunctor_2122_; lean_object* v_toBind_2123_; lean_object* v_toPure_2124_; lean_object* v_map_2125_; lean_object* v___f_2126_; lean_object* v_msg_2127_; lean_object* v___f_2128_; lean_object* v___f_2129_; lean_object* v___f_2130_; lean_object* v___f_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_toApplicative_2121_ = lean_ctor_get(v_inst_2110_, 0);
v_toFunctor_2122_ = lean_ctor_get(v_toApplicative_2121_, 0);
v_toBind_2123_ = lean_ctor_get(v_inst_2110_, 1);
lean_inc_n(v_toBind_2123_, 3);
v_toPure_2124_ = lean_ctor_get(v_toApplicative_2121_, 1);
lean_inc_n(v_toPure_2124_, 5);
v_map_2125_ = lean_ctor_get(v_toFunctor_2122_, 0);
lean_inc(v_map_2125_);
v___f_2126_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2127_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2127_, 0, v_toPure_2124_);
lean_inc(v_inst_2114_);
lean_inc(v_cls_2117_);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2128_, 0, v_toPure_2124_);
lean_closure_set(v___f_2128_, 1, v_cls_2117_);
lean_closure_set(v___f_2128_, 2, v_toBind_2123_);
lean_closure_set(v___f_2128_, 3, v_inst_2114_);
v___f_2129_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2129_, 0, v_toPure_2124_);
v___f_2130_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2130_, 0, v_toPure_2124_);
v___f_2131_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2132_ = lean_box(v_collapsed_2119_);
v___f_2133_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2133_, 0, v_k_2118_);
lean_closure_set(v___f_2133_, 1, v_inst_2111_);
lean_closure_set(v___f_2133_, 2, v_inst_2115_);
lean_closure_set(v___f_2133_, 3, v_inst_2110_);
lean_closure_set(v___f_2133_, 4, v_inst_2112_);
lean_closure_set(v___f_2133_, 5, v_inst_2113_);
lean_closure_set(v___f_2133_, 6, v___f_2131_);
lean_closure_set(v___f_2133_, 7, v_cls_2117_);
lean_closure_set(v___f_2133_, 8, v___x_2132_);
lean_closure_set(v___f_2133_, 9, v_tag_2120_);
lean_closure_set(v___f_2133_, 10, v_msg_2127_);
lean_closure_set(v___f_2133_, 11, v_toBind_2123_);
lean_closure_set(v___f_2133_, 12, v___f_2130_);
lean_closure_set(v___f_2133_, 13, v___f_2129_);
lean_closure_set(v___f_2133_, 14, v_inst_2116_);
lean_closure_set(v___f_2133_, 15, v_toPure_2124_);
lean_closure_set(v___f_2133_, 16, v___f_2128_);
v___x_2134_ = lean_apply_4(v_toBind_2123_, lean_box(0), lean_box(0), v_inst_2114_, v___f_2133_);
v___x_2135_ = lean_apply_4(v_map_2125_, lean_box(0), lean_box(0), v___f_2126_, v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_cls_2143_, lean_object* v_k_2144_, lean_object* v_collapsed_2145_, lean_object* v_tag_2146_){
_start:
{
uint8_t v_collapsed_boxed_2147_; lean_object* v_res_2148_; 
v_collapsed_boxed_2147_ = lean_unbox(v_collapsed_2145_);
v_res_2148_ = l_Lean_withTraceNode_x27___redArg(v_inst_2136_, v_inst_2137_, v_inst_2138_, v_inst_2139_, v_inst_2140_, v_inst_2141_, v_inst_2142_, v_cls_2143_, v_k_2144_, v_collapsed_boxed_2147_, v_tag_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object* v_00_u03b1_2149_, lean_object* v_m_2150_, lean_object* v_inst_2151_, lean_object* v_inst_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_, lean_object* v_inst_2155_, lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_cls_2158_, lean_object* v_k_2159_, uint8_t v_collapsed_2160_, lean_object* v_tag_2161_){
_start:
{
lean_object* v_toApplicative_2162_; lean_object* v_toFunctor_2163_; lean_object* v_toBind_2164_; lean_object* v_toPure_2165_; lean_object* v_map_2166_; lean_object* v___f_2167_; lean_object* v_msg_2168_; lean_object* v___f_2169_; lean_object* v___f_2170_; lean_object* v___f_2171_; lean_object* v___f_2172_; lean_object* v___x_2173_; lean_object* v___f_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_toApplicative_2162_ = lean_ctor_get(v_inst_2151_, 0);
v_toFunctor_2163_ = lean_ctor_get(v_toApplicative_2162_, 0);
v_toBind_2164_ = lean_ctor_get(v_inst_2151_, 1);
lean_inc_n(v_toBind_2164_, 3);
v_toPure_2165_ = lean_ctor_get(v_toApplicative_2162_, 1);
lean_inc_n(v_toPure_2165_, 5);
v_map_2166_ = lean_ctor_get(v_toFunctor_2163_, 0);
lean_inc(v_map_2166_);
v___f_2167_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2168_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2168_, 0, v_toPure_2165_);
lean_inc(v_inst_2155_);
lean_inc(v_cls_2158_);
v___f_2169_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2169_, 0, v_toPure_2165_);
lean_closure_set(v___f_2169_, 1, v_cls_2158_);
lean_closure_set(v___f_2169_, 2, v_toBind_2164_);
lean_closure_set(v___f_2169_, 3, v_inst_2155_);
v___f_2170_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2170_, 0, v_toPure_2165_);
v___f_2171_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2171_, 0, v_toPure_2165_);
v___f_2172_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2173_ = lean_box(v_collapsed_2160_);
v___f_2174_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2174_, 0, v_k_2159_);
lean_closure_set(v___f_2174_, 1, v_inst_2152_);
lean_closure_set(v___f_2174_, 2, v_inst_2156_);
lean_closure_set(v___f_2174_, 3, v_inst_2151_);
lean_closure_set(v___f_2174_, 4, v_inst_2153_);
lean_closure_set(v___f_2174_, 5, v_inst_2154_);
lean_closure_set(v___f_2174_, 6, v___f_2172_);
lean_closure_set(v___f_2174_, 7, v_cls_2158_);
lean_closure_set(v___f_2174_, 8, v___x_2173_);
lean_closure_set(v___f_2174_, 9, v_tag_2161_);
lean_closure_set(v___f_2174_, 10, v_msg_2168_);
lean_closure_set(v___f_2174_, 11, v_toBind_2164_);
lean_closure_set(v___f_2174_, 12, v___f_2171_);
lean_closure_set(v___f_2174_, 13, v___f_2170_);
lean_closure_set(v___f_2174_, 14, v_inst_2157_);
lean_closure_set(v___f_2174_, 15, v_toPure_2165_);
lean_closure_set(v___f_2174_, 16, v___f_2169_);
v___x_2175_ = lean_apply_4(v_toBind_2164_, lean_box(0), lean_box(0), v_inst_2155_, v___f_2174_);
v___x_2176_ = lean_apply_4(v_map_2166_, lean_box(0), lean_box(0), v___f_2167_, v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_m_2178_, lean_object* v_inst_2179_, lean_object* v_inst_2180_, lean_object* v_inst_2181_, lean_object* v_inst_2182_, lean_object* v_inst_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_cls_2186_, lean_object* v_k_2187_, lean_object* v_collapsed_2188_, lean_object* v_tag_2189_){
_start:
{
uint8_t v_collapsed_boxed_2190_; lean_object* v_res_2191_; 
v_collapsed_boxed_2190_ = lean_unbox(v_collapsed_2188_);
v_res_2191_ = l_Lean_withTraceNode_x27(v_00_u03b1_2177_, v_m_2178_, v_inst_2179_, v_inst_2180_, v_inst_2181_, v_inst_2182_, v_inst_2183_, v_inst_2184_, v_inst_2185_, v_cls_2186_, v_k_2187_, v_collapsed_boxed_2190_, v_tag_2189_);
return v_res_2191_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__4(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__3));
v___x_2201_ = l_Lean_mkAtom(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__5(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__4, &l_Lean_registerTraceClass___auto__1___closed__4_once, _init_l_Lean_registerTraceClass___auto__1___closed__4);
v___x_2203_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2204_ = lean_array_push(v___x_2203_, v___x_2202_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__6(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__5, &l_Lean_registerTraceClass___auto__1___closed__5_once, _init_l_Lean_registerTraceClass___auto__1___closed__5);
v___x_2206_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__2));
v___x_2207_ = lean_box(2);
v___x_2208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2206_);
lean_ctor_set(v___x_2208_, 2, v___x_2205_);
return v___x_2208_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__7(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__6, &l_Lean_registerTraceClass___auto__1___closed__6_once, _init_l_Lean_registerTraceClass___auto__1___closed__6);
v___x_2210_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_2211_ = lean_array_push(v___x_2210_, v___x_2209_);
return v___x_2211_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2212_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__7, &l_Lean_registerTraceClass___auto__1___closed__7_once, _init_l_Lean_registerTraceClass___auto__1___closed__7);
v___x_2213_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_2214_ = lean_box(2);
v___x_2215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___x_2213_);
lean_ctor_set(v___x_2215_, 2, v___x_2212_);
return v___x_2215_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__8, &l_Lean_registerTraceClass___auto__1___closed__8_once, _init_l_Lean_registerTraceClass___auto__1___closed__8);
v___x_2217_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2218_ = lean_array_push(v___x_2217_, v___x_2216_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2219_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__9, &l_Lean_registerTraceClass___auto__1___closed__9_once, _init_l_Lean_registerTraceClass___auto__1___closed__9);
v___x_2220_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2221_ = lean_box(2);
v___x_2222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___x_2220_);
lean_ctor_set(v___x_2222_, 2, v___x_2219_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__11(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__10, &l_Lean_registerTraceClass___auto__1___closed__10_once, _init_l_Lean_registerTraceClass___auto__1___closed__10);
v___x_2224_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2225_ = lean_array_push(v___x_2224_, v___x_2223_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2226_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__11, &l_Lean_registerTraceClass___auto__1___closed__11_once, _init_l_Lean_registerTraceClass___auto__1___closed__11);
v___x_2227_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_2228_ = lean_box(2);
v___x_2229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v___x_2227_);
lean_ctor_set(v___x_2229_, 2, v___x_2226_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__12, &l_Lean_registerTraceClass___auto__1___closed__12_once, _init_l_Lean_registerTraceClass___auto__1___closed__12);
v___x_2231_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2232_ = lean_array_push(v___x_2231_, v___x_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2233_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__13, &l_Lean_registerTraceClass___auto__1___closed__13_once, _init_l_Lean_registerTraceClass___auto__1___closed__13);
v___x_2234_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_2235_ = lean_box(2);
v___x_2236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set(v___x_2236_, 1, v___x_2234_);
lean_ctor_set(v___x_2236_, 2, v___x_2233_);
return v___x_2236_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1(void){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__14, &l_Lean_registerTraceClass___auto__1___closed__14_once, _init_l_Lean_registerTraceClass___auto__1___closed__14);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
if (lean_obj_tag(v_x_2239_) == 0)
{
return v_x_2238_;
}
else
{
lean_object* v_key_2240_; lean_object* v_value_2241_; lean_object* v_tail_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2268_; 
v_key_2240_ = lean_ctor_get(v_x_2239_, 0);
v_value_2241_ = lean_ctor_get(v_x_2239_, 1);
v_tail_2242_ = lean_ctor_get(v_x_2239_, 2);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_x_2239_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2244_ = v_x_2239_;
v_isShared_2245_ = v_isSharedCheck_2268_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_tail_2242_);
lean_inc(v_value_2241_);
lean_inc(v_key_2240_);
lean_dec(v_x_2239_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2268_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; uint64_t v___y_2248_; 
v___x_2246_ = lean_array_get_size(v_x_2238_);
if (lean_obj_tag(v_key_2240_) == 0)
{
uint64_t v___x_2266_; 
v___x_2266_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2248_ = v___x_2266_;
goto v___jp_2247_;
}
else
{
uint64_t v_hash_2267_; 
v_hash_2267_ = lean_ctor_get_uint64(v_key_2240_, sizeof(void*)*2);
v___y_2248_ = v_hash_2267_;
goto v___jp_2247_;
}
v___jp_2247_:
{
uint64_t v___x_2249_; uint64_t v___x_2250_; uint64_t v_fold_2251_; uint64_t v___x_2252_; uint64_t v___x_2253_; uint64_t v___x_2254_; size_t v___x_2255_; size_t v___x_2256_; size_t v___x_2257_; size_t v___x_2258_; size_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2249_ = 32ULL;
v___x_2250_ = lean_uint64_shift_right(v___y_2248_, v___x_2249_);
v_fold_2251_ = lean_uint64_xor(v___y_2248_, v___x_2250_);
v___x_2252_ = 16ULL;
v___x_2253_ = lean_uint64_shift_right(v_fold_2251_, v___x_2252_);
v___x_2254_ = lean_uint64_xor(v_fold_2251_, v___x_2253_);
v___x_2255_ = lean_uint64_to_usize(v___x_2254_);
v___x_2256_ = lean_usize_of_nat(v___x_2246_);
v___x_2257_ = ((size_t)1ULL);
v___x_2258_ = lean_usize_sub(v___x_2256_, v___x_2257_);
v___x_2259_ = lean_usize_land(v___x_2255_, v___x_2258_);
v___x_2260_ = lean_array_uget_borrowed(v_x_2238_, v___x_2259_);
lean_inc(v___x_2260_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 2, v___x_2260_);
v___x_2262_ = v___x_2244_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_key_2240_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_value_2241_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_array_uset(v_x_2238_, v___x_2259_, v___x_2262_);
v_x_2238_ = v___x_2263_;
v_x_2239_ = v_tail_2242_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object* v_i_2269_, lean_object* v_source_2270_, lean_object* v_target_2271_){
_start:
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = lean_array_get_size(v_source_2270_);
v___x_2273_ = lean_nat_dec_lt(v_i_2269_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_dec_ref(v_source_2270_);
lean_dec(v_i_2269_);
return v_target_2271_;
}
else
{
lean_object* v_es_2274_; lean_object* v___x_2275_; lean_object* v_source_2276_; lean_object* v_target_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_es_2274_ = lean_array_fget(v_source_2270_, v_i_2269_);
v___x_2275_ = lean_box(0);
v_source_2276_ = lean_array_fset(v_source_2270_, v_i_2269_, v___x_2275_);
v_target_2277_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_2271_, v_es_2274_);
v___x_2278_ = lean_unsigned_to_nat(1u);
v___x_2279_ = lean_nat_add(v_i_2269_, v___x_2278_);
lean_dec(v_i_2269_);
v_i_2269_ = v___x_2279_;
v_source_2270_ = v_source_2276_;
v_target_2271_ = v_target_2277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object* v_data_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v_nbuckets_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2282_ = lean_array_get_size(v_data_2281_);
v___x_2283_ = lean_unsigned_to_nat(2u);
v_nbuckets_2284_ = lean_nat_mul(v___x_2282_, v___x_2283_);
v___x_2285_ = lean_unsigned_to_nat(0u);
v___x_2286_ = lean_box(0);
v___x_2287_ = lean_mk_array(v_nbuckets_2284_, v___x_2286_);
v___x_2288_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_2285_, v_data_2281_, v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object* v_m_2289_, lean_object* v_a_2290_, lean_object* v_b_2291_){
_start:
{
lean_object* v_size_2292_; lean_object* v_buckets_2293_; lean_object* v___x_2294_; uint64_t v___y_2296_; 
v_size_2292_ = lean_ctor_get(v_m_2289_, 0);
v_buckets_2293_ = lean_ctor_get(v_m_2289_, 1);
v___x_2294_ = lean_array_get_size(v_buckets_2293_);
if (lean_obj_tag(v_a_2290_) == 0)
{
uint64_t v___x_2333_; 
v___x_2333_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2296_ = v___x_2333_;
goto v___jp_2295_;
}
else
{
uint64_t v_hash_2334_; 
v_hash_2334_ = lean_ctor_get_uint64(v_a_2290_, sizeof(void*)*2);
v___y_2296_ = v_hash_2334_;
goto v___jp_2295_;
}
v___jp_2295_:
{
uint64_t v___x_2297_; uint64_t v___x_2298_; uint64_t v_fold_2299_; uint64_t v___x_2300_; uint64_t v___x_2301_; uint64_t v___x_2302_; size_t v___x_2303_; size_t v___x_2304_; size_t v___x_2305_; size_t v___x_2306_; size_t v___x_2307_; lean_object* v_bkt_2308_; uint8_t v___x_2309_; 
v___x_2297_ = 32ULL;
v___x_2298_ = lean_uint64_shift_right(v___y_2296_, v___x_2297_);
v_fold_2299_ = lean_uint64_xor(v___y_2296_, v___x_2298_);
v___x_2300_ = 16ULL;
v___x_2301_ = lean_uint64_shift_right(v_fold_2299_, v___x_2300_);
v___x_2302_ = lean_uint64_xor(v_fold_2299_, v___x_2301_);
v___x_2303_ = lean_uint64_to_usize(v___x_2302_);
v___x_2304_ = lean_usize_of_nat(v___x_2294_);
v___x_2305_ = ((size_t)1ULL);
v___x_2306_ = lean_usize_sub(v___x_2304_, v___x_2305_);
v___x_2307_ = lean_usize_land(v___x_2303_, v___x_2306_);
v_bkt_2308_ = lean_array_uget_borrowed(v_buckets_2293_, v___x_2307_);
v___x_2309_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_2290_, v_bkt_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2330_; 
lean_inc_ref(v_buckets_2293_);
lean_inc(v_size_2292_);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_m_2289_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; lean_object* v_unused_2332_; 
v_unused_2331_ = lean_ctor_get(v_m_2289_, 1);
lean_dec(v_unused_2331_);
v_unused_2332_ = lean_ctor_get(v_m_2289_, 0);
lean_dec(v_unused_2332_);
v___x_2311_ = v_m_2289_;
v_isShared_2312_ = v_isSharedCheck_2330_;
goto v_resetjp_2310_;
}
else
{
lean_dec(v_m_2289_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2330_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v_size_x27_2314_; lean_object* v___x_2315_; lean_object* v_buckets_x27_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2313_ = lean_unsigned_to_nat(1u);
v_size_x27_2314_ = lean_nat_add(v_size_2292_, v___x_2313_);
lean_dec(v_size_2292_);
lean_inc(v_bkt_2308_);
v___x_2315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2315_, 0, v_a_2290_);
lean_ctor_set(v___x_2315_, 1, v_b_2291_);
lean_ctor_set(v___x_2315_, 2, v_bkt_2308_);
v_buckets_x27_2316_ = lean_array_uset(v_buckets_2293_, v___x_2307_, v___x_2315_);
v___x_2317_ = lean_unsigned_to_nat(4u);
v___x_2318_ = lean_nat_mul(v_size_x27_2314_, v___x_2317_);
v___x_2319_ = lean_unsigned_to_nat(3u);
v___x_2320_ = lean_nat_div(v___x_2318_, v___x_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_array_get_size(v_buckets_x27_2316_);
v___x_2322_ = lean_nat_dec_le(v___x_2320_, v___x_2321_);
lean_dec(v___x_2320_);
if (v___x_2322_ == 0)
{
lean_object* v_val_2323_; lean_object* v___x_2325_; 
v_val_2323_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_2316_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v_val_2323_);
lean_ctor_set(v___x_2311_, 0, v_size_x27_2314_);
v___x_2325_ = v___x_2311_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_size_x27_2314_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_val_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
else
{
lean_object* v___x_2328_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v_buckets_x27_2316_);
lean_ctor_set(v___x_2311_, 0, v_size_x27_2314_);
v___x_2328_ = v___x_2311_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_size_x27_2314_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_buckets_x27_2316_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
else
{
lean_dec(v_b_2291_);
lean_dec(v_a_2290_);
return v_m_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object* v_traceClassName_2338_, uint8_t v_inherited_2339_, lean_object* v_ref_2340_){
_start:
{
lean_object* v___x_2342_; lean_object* v_optionName_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2342_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v_optionName_2343_ = l_Lean_Name_append(v___x_2342_, v_traceClassName_2338_);
v___x_2344_ = ((lean_object*)(l_Lean_registerTraceClass___closed__0));
v___x_2345_ = ((lean_object*)(l_Lean_registerTraceClass___closed__1));
v___x_2346_ = lean_box(0);
lean_inc_n(v_optionName_2343_, 2);
v___x_2347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2347_, 0, v_optionName_2343_);
lean_ctor_set(v___x_2347_, 1, v_ref_2340_);
lean_ctor_set(v___x_2347_, 2, v___x_2344_);
lean_ctor_set(v___x_2347_, 3, v___x_2345_);
lean_ctor_set(v___x_2347_, 4, v___x_2346_);
v___x_2348_ = lean_register_option(v_optionName_2343_, v___x_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2364_; 
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v___x_2348_, 0);
lean_dec(v_unused_2365_);
v___x_2350_ = v___x_2348_;
v_isShared_2351_ = v_isSharedCheck_2364_;
goto v_resetjp_2349_;
}
else
{
lean_dec(v___x_2348_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2364_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
if (v_inherited_2339_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
lean_dec(v_optionName_2343_);
v___x_2352_ = lean_box(0);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2352_);
v___x_2354_ = v___x_2350_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
else
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2356_ = l_Lean_inheritedTraceOptions;
v___x_2357_ = lean_st_ref_take(v___x_2356_);
v___x_2358_ = lean_box(0);
v___x_2359_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2357_, v_optionName_2343_, v___x_2358_);
v___x_2360_ = lean_st_ref_set(v___x_2356_, v___x_2359_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2360_);
v___x_2362_ = v___x_2350_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_dec(v_optionName_2343_);
return v___x_2348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object* v_traceClassName_2366_, lean_object* v_inherited_2367_, lean_object* v_ref_2368_, lean_object* v_a_2369_){
_start:
{
uint8_t v_inherited_boxed_2370_; lean_object* v_res_2371_; 
v_inherited_boxed_2370_ = lean_unbox(v_inherited_2367_);
v_res_2371_ = l_Lean_registerTraceClass(v_traceClassName_2366_, v_inherited_boxed_2370_, v_ref_2368_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(lean_object* v_00_u03b2_2372_, lean_object* v_m_2373_, lean_object* v_a_2374_, lean_object* v_b_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v_m_2373_, v_a_2374_, v_b_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object* v_00_u03b2_2377_, lean_object* v_data_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_data_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2380_, lean_object* v_i_2381_, lean_object* v_source_2382_, lean_object* v_target_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_i_2381_, v_source_2382_, v_target_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2386_, v_x_2387_);
return v___x_2388_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_2399_ = l_String_toRawSubstring_x27(v___x_2398_);
return v___x_2399_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12));
v___x_2405_ = l_String_toRawSubstring_x27(v___x_2404_);
return v___x_2405_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18));
v___x_2412_ = l_String_toRawSubstring_x27(v___x_2411_);
return v___x_2412_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31(void){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Array_mkArray0(lean_box(0));
return v___x_2440_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41(void){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40));
v___x_2467_ = l_String_toRawSubstring_x27(v___x_2466_);
return v___x_2467_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57));
v___x_2503_ = l_String_toRawSubstring_x27(v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object* v_id_2525_, lean_object* v_s_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v_msg_2625_; lean_object* v_quotContext_2626_; lean_object* v_currMacroScope_2627_; lean_object* v_ref_2628_; lean_object* v___y_2629_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
lean_inc(v_s_2526_);
v___x_2675_ = l_Lean_Syntax_getKind(v_s_2526_);
v___x_2676_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49));
v___x_2677_ = lean_name_eq(v___x_2675_, v___x_2676_);
lean_dec(v___x_2675_);
if (v___x_2677_ == 0)
{
lean_object* v_quotContext_2678_; lean_object* v_currMacroScope_2679_; lean_object* v_ref_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_quotContext_2678_ = lean_ctor_get(v_a_2527_, 1);
v_currMacroScope_2679_ = lean_ctor_get(v_a_2527_, 2);
v_ref_2680_ = lean_ctor_get(v_a_2527_, 5);
v___x_2681_ = l_Lean_SourceInfo_fromRef(v_ref_2680_, v___x_2677_);
v___x_2682_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51));
v___x_2683_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52));
v___x_2684_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
lean_inc_n(v___x_2681_, 8);
v___x_2685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2681_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2687_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2688_ = lean_box(0);
lean_inc_n(v_currMacroScope_2679_, 3);
lean_inc_n(v_quotContext_2678_, 3);
v___x_2689_ = l_Lean_addMacroScope(v_quotContext_2678_, v___x_2688_, v_currMacroScope_2679_);
v___x_2690_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55));
v___x_2691_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2681_);
lean_ctor_set(v___x_2691_, 1, v___x_2687_);
lean_ctor_set(v___x_2691_, 2, v___x_2689_);
lean_ctor_set(v___x_2691_, 3, v___x_2690_);
v___x_2692_ = l_Lean_Syntax_node1(v___x_2681_, v___x_2686_, v___x_2691_);
v___x_2693_ = l_Lean_Syntax_node2(v___x_2681_, v___x_2683_, v___x_2685_, v___x_2692_);
v___x_2694_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56));
v___x_2695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2681_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2697_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58);
v___x_2698_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59));
v___x_2699_ = l_Lean_addMacroScope(v_quotContext_2678_, v___x_2698_, v_currMacroScope_2679_);
v___x_2700_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64));
v___x_2701_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2681_);
lean_ctor_set(v___x_2701_, 1, v___x_2697_);
lean_ctor_set(v___x_2701_, 2, v___x_2699_);
lean_ctor_set(v___x_2701_, 3, v___x_2700_);
v___x_2702_ = l_Lean_Syntax_node1(v___x_2681_, v___x_2696_, v___x_2701_);
v___x_2703_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2681_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = l_Lean_Syntax_node5(v___x_2681_, v___x_2682_, v___x_2693_, v_s_2526_, v___x_2695_, v___x_2702_, v___x_2704_);
v_msg_2625_ = v___x_2705_;
v_quotContext_2626_ = v_quotContext_2678_;
v_currMacroScope_2627_ = v_currMacroScope_2679_;
v_ref_2628_ = v_ref_2680_;
v___y_2629_ = v_a_2528_;
goto v___jp_2624_;
}
else
{
lean_object* v_quotContext_2706_; lean_object* v_currMacroScope_2707_; lean_object* v_ref_2708_; uint8_t v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_quotContext_2706_ = lean_ctor_get(v_a_2527_, 1);
v_currMacroScope_2707_ = lean_ctor_get(v_a_2527_, 2);
v_ref_2708_ = lean_ctor_get(v_a_2527_, 5);
v___x_2709_ = 0;
v___x_2710_ = l_Lean_SourceInfo_fromRef(v_ref_2708_, v___x_2709_);
v___x_2711_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66));
v___x_2712_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67));
lean_inc(v___x_2710_);
v___x_2713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2710_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Lean_Syntax_node2(v___x_2710_, v___x_2711_, v___x_2713_, v_s_2526_);
lean_inc(v_currMacroScope_2707_);
lean_inc(v_quotContext_2706_);
v_msg_2625_ = v___x_2714_;
v_quotContext_2626_ = v_quotContext_2706_;
v_currMacroScope_2627_ = v_currMacroScope_2707_;
v_ref_2628_ = v_ref_2708_;
v___y_2629_ = v_a_2528_;
goto v___jp_2624_;
}
v___jp_2529_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_inc_n(v___y_2549_, 8);
lean_inc(v___y_2552_);
lean_inc_n(v___y_2543_, 29);
v___x_2554_ = l_Lean_Syntax_node5(v___y_2543_, v___y_2552_, v___y_2538_, v___y_2549_, v___y_2549_, v___y_2539_, v___y_2553_);
lean_inc(v___y_2534_);
v___x_2555_ = l_Lean_Syntax_node1(v___y_2543_, v___y_2534_, v___x_2554_);
lean_inc(v___y_2542_);
v___x_2556_ = l_Lean_Syntax_node4(v___y_2543_, v___y_2542_, v___y_2550_, v___y_2549_, v___y_2530_, v___x_2555_);
lean_inc_n(v___y_2547_, 3);
v___x_2557_ = l_Lean_Syntax_node2(v___y_2543_, v___y_2547_, v___x_2556_, v___y_2549_);
v___x_2558_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0));
lean_inc_ref_n(v___y_2540_, 7);
lean_inc_ref_n(v___y_2548_, 7);
lean_inc_ref_n(v___y_2551_, 10);
v___x_2559_ = l_Lean_Name_mkStr4(v___y_2551_, v___y_2548_, v___y_2540_, v___x_2558_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1));
v___x_2561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___y_2543_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2));
v___x_2563_ = l_Lean_Name_mkStr4(v___y_2551_, v___y_2548_, v___y_2540_, v___x_2562_);
v___x_2564_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3));
v___x_2565_ = l_Lean_Name_mkStr4(v___y_2551_, v___y_2548_, v___y_2540_, v___x_2564_);
v___x_2566_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4));
v___x_2567_ = l_Lean_Name_mkStr4(v___y_2551_, v___y_2548_, v___y_2540_, v___x_2566_);
v___x_2568_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
v___x_2569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___y_2543_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2571_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2572_ = lean_box(0);
lean_inc_n(v___y_2545_, 2);
lean_inc_n(v___y_2535_, 2);
v___x_2573_ = l_Lean_addMacroScope(v___y_2535_, v___x_2572_, v___y_2545_);
v___x_2574_ = l_Lean_Name_mkStr1(v___y_2551_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_inc_n(v___y_2533_, 2);
v___x_2576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v___y_2533_);
v___x_2577_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2577_, 0, v___y_2543_);
lean_ctor_set(v___x_2577_, 1, v___x_2571_);
lean_ctor_set(v___x_2577_, 2, v___x_2573_);
lean_ctor_set(v___x_2577_, 3, v___x_2576_);
v___x_2578_ = l_Lean_Syntax_node1(v___y_2543_, v___x_2570_, v___x_2577_);
v___x_2579_ = l_Lean_Syntax_node2(v___y_2543_, v___x_2567_, v___x_2569_, v___x_2578_);
v___x_2580_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9));
v___x_2581_ = l_Lean_Name_mkStr4(v___y_2551_, v___y_2548_, v___y_2540_, v___x_2580_);
v___x_2582_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10));
v___x_2583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___y_2543_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11));
v___x_2585_ = l_Lean_Name_mkStr4(v___y_2551_, v___y_2548_, v___y_2540_, v___x_2584_);
v___x_2586_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13);
v___x_2587_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14));
v___x_2588_ = l_Lean_Name_mkStr2(v___y_2551_, v___x_2587_);
lean_inc(v___x_2588_);
v___x_2589_ = l_Lean_addMacroScope(v___y_2535_, v___x_2588_, v___y_2545_);
v___x_2590_ = lean_box(0);
v___x_2591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2588_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
lean_ctor_set(v___x_2592_, 1, v___y_2533_);
v___x_2593_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2593_, 0, v___y_2543_);
lean_ctor_set(v___x_2593_, 1, v___x_2586_);
lean_ctor_set(v___x_2593_, 2, v___x_2589_);
lean_ctor_set(v___x_2593_, 3, v___x_2592_);
lean_inc(v___y_2532_);
lean_inc_n(v___y_2544_, 4);
v___x_2594_ = l_Lean_Syntax_node1(v___y_2543_, v___y_2544_, v___y_2532_);
lean_inc(v___x_2585_);
v___x_2595_ = l_Lean_Syntax_node2(v___y_2543_, v___x_2585_, v___x_2593_, v___x_2594_);
v___x_2596_ = l_Lean_Syntax_node2(v___y_2543_, v___x_2581_, v___x_2583_, v___x_2595_);
v___x_2597_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___y_2543_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = l_Lean_Syntax_node3(v___y_2543_, v___x_2565_, v___x_2579_, v___x_2596_, v___x_2598_);
v___x_2600_ = l_Lean_Syntax_node2(v___y_2543_, v___x_2563_, v___y_2549_, v___x_2599_);
v___x_2601_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___y_2543_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17));
v___x_2604_ = l_Lean_Name_mkStr4(v___y_2551_, v___y_2548_, v___y_2540_, v___x_2603_);
v___x_2605_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19);
v___x_2606_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20));
v___x_2607_ = l_Lean_Name_mkStr2(v___y_2551_, v___x_2606_);
lean_inc(v___x_2607_);
v___x_2608_ = l_Lean_addMacroScope(v___y_2535_, v___x_2607_, v___y_2545_);
v___x_2609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2590_);
v___x_2610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___y_2533_);
v___x_2611_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2611_, 0, v___y_2543_);
lean_ctor_set(v___x_2611_, 1, v___x_2605_);
lean_ctor_set(v___x_2611_, 2, v___x_2608_);
lean_ctor_set(v___x_2611_, 3, v___x_2610_);
v___x_2612_ = l_Lean_Syntax_node2(v___y_2543_, v___y_2544_, v___y_2532_, v___y_2546_);
v___x_2613_ = l_Lean_Syntax_node2(v___y_2543_, v___x_2585_, v___x_2611_, v___x_2612_);
v___x_2614_ = l_Lean_Syntax_node1(v___y_2543_, v___x_2604_, v___x_2613_);
v___x_2615_ = l_Lean_Syntax_node2(v___y_2543_, v___y_2547_, v___x_2614_, v___y_2549_);
v___x_2616_ = l_Lean_Syntax_node1(v___y_2543_, v___y_2544_, v___x_2615_);
lean_inc_n(v___y_2541_, 2);
v___x_2617_ = l_Lean_Syntax_node1(v___y_2543_, v___y_2541_, v___x_2616_);
v___x_2618_ = l_Lean_Syntax_node6(v___y_2543_, v___x_2559_, v___x_2561_, v___x_2600_, v___x_2602_, v___x_2617_, v___y_2549_, v___y_2549_);
v___x_2619_ = l_Lean_Syntax_node2(v___y_2543_, v___y_2547_, v___x_2618_, v___y_2549_);
v___x_2620_ = l_Lean_Syntax_node2(v___y_2543_, v___y_2544_, v___x_2557_, v___x_2619_);
v___x_2621_ = l_Lean_Syntax_node1(v___y_2543_, v___y_2541_, v___x_2620_);
lean_inc(v___y_2536_);
v___x_2622_ = l_Lean_Syntax_node2(v___y_2543_, v___y_2536_, v___y_2537_, v___x_2621_);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v___y_2531_);
return v___x_2623_;
}
v___jp_2624_:
{
uint8_t v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2630_ = 0;
v___x_2631_ = l_Lean_SourceInfo_fromRef(v_ref_2628_, v___x_2630_);
v___x_2632_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0));
v___x_2633_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1));
v___x_2634_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__0));
v___x_2635_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22));
v___x_2636_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23));
lean_inc_n(v___x_2631_, 7);
v___x_2637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2631_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25));
v___x_2639_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2640_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27));
v___x_2641_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2642_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
v___x_2643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2631_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31);
v___x_2645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2631_);
lean_ctor_set(v___x_2645_, 1, v___x_2639_);
lean_ctor_set(v___x_2645_, 2, v___x_2644_);
v___x_2646_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33));
lean_inc_ref(v___x_2645_);
v___x_2647_ = l_Lean_Syntax_node1(v___x_2631_, v___x_2646_, v___x_2645_);
v___x_2648_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35));
v___x_2649_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37));
v___x_2650_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39));
v___x_2651_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41);
v___x_2652_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42));
lean_inc(v_currMacroScope_2627_);
lean_inc(v_quotContext_2626_);
v___x_2653_ = l_Lean_addMacroScope(v_quotContext_2626_, v___x_2652_, v_currMacroScope_2627_);
v___x_2654_ = lean_box(0);
v___x_2655_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2631_);
lean_ctor_set(v___x_2655_, 1, v___x_2651_);
lean_ctor_set(v___x_2655_, 2, v___x_2653_);
lean_ctor_set(v___x_2655_, 3, v___x_2654_);
lean_inc_ref(v___x_2655_);
v___x_2656_ = l_Lean_Syntax_node1(v___x_2631_, v___x_2650_, v___x_2655_);
v___x_2657_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43));
v___x_2658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2631_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___x_2659_ = l_Lean_Syntax_getId(v_id_2525_);
v___x_2660_ = lean_erase_macro_scopes(v___x_2659_);
lean_inc(v___x_2660_);
v___x_2661_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2654_, v___x_2660_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_quoteNameMk(v___x_2660_);
v___y_2530_ = v___x_2647_;
v___y_2531_ = v___y_2629_;
v___y_2532_ = v___x_2655_;
v___y_2533_ = v___x_2654_;
v___y_2534_ = v___x_2648_;
v___y_2535_ = v_quotContext_2626_;
v___y_2536_ = v___x_2635_;
v___y_2537_ = v___x_2637_;
v___y_2538_ = v___x_2656_;
v___y_2539_ = v___x_2658_;
v___y_2540_ = v___x_2634_;
v___y_2541_ = v___x_2638_;
v___y_2542_ = v___x_2641_;
v___y_2543_ = v___x_2631_;
v___y_2544_ = v___x_2639_;
v___y_2545_ = v_currMacroScope_2627_;
v___y_2546_ = v_msg_2625_;
v___y_2547_ = v___x_2640_;
v___y_2548_ = v___x_2633_;
v___y_2549_ = v___x_2645_;
v___y_2550_ = v___x_2643_;
v___y_2551_ = v___x_2632_;
v___y_2552_ = v___x_2649_;
v___y_2553_ = v___x_2662_;
goto v___jp_2529_;
}
else
{
lean_object* v_val_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec(v___x_2660_);
v_val_2663_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_val_2663_);
lean_dec_ref(v___x_2661_);
v___x_2664_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45));
v___x_2665_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46));
v___x_2666_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47));
v___x_2667_ = lean_string_intercalate(v___x_2666_, v_val_2663_);
v___x_2668_ = lean_string_append(v___x_2665_, v___x_2667_);
lean_dec_ref(v___x_2667_);
v___x_2669_ = lean_box(2);
v___x_2670_ = l_Lean_Syntax_mkNameLit(v___x_2668_, v___x_2669_);
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_2672_ = lean_mk_empty_array_with_capacity(v___x_2671_);
v___x_2673_ = lean_array_push(v___x_2672_, v___x_2670_);
v___x_2674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2669_);
lean_ctor_set(v___x_2674_, 1, v___x_2664_);
lean_ctor_set(v___x_2674_, 2, v___x_2673_);
v___y_2530_ = v___x_2647_;
v___y_2531_ = v___y_2629_;
v___y_2532_ = v___x_2655_;
v___y_2533_ = v___x_2654_;
v___y_2534_ = v___x_2648_;
v___y_2535_ = v_quotContext_2626_;
v___y_2536_ = v___x_2635_;
v___y_2537_ = v___x_2637_;
v___y_2538_ = v___x_2656_;
v___y_2539_ = v___x_2658_;
v___y_2540_ = v___x_2634_;
v___y_2541_ = v___x_2638_;
v___y_2542_ = v___x_2641_;
v___y_2543_ = v___x_2631_;
v___y_2544_ = v___x_2639_;
v___y_2545_ = v_currMacroScope_2627_;
v___y_2546_ = v_msg_2625_;
v___y_2547_ = v___x_2640_;
v___y_2548_ = v___x_2633_;
v___y_2549_ = v___x_2645_;
v___y_2550_ = v___x_2643_;
v___y_2551_ = v___x_2632_;
v___y_2552_ = v___x_2649_;
v___y_2553_ = v___x_2674_;
goto v___jp_2529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object* v_id_2715_, lean_object* v_s_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v_id_2715_, v_s_2716_, v_a_2717_, v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_id_2715_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object* v_x_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = ((lean_object*)(l_Lean_doElemTrace_x5b___x5d_____00__closed__1));
lean_inc(v_x_2774_);
v___x_2778_ = l_Lean_Syntax_isOfKind(v_x_2774_, v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_dec(v_x_2774_);
v___x_2779_ = lean_box(1);
v___x_2780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
lean_ctor_set(v___x_2780_, 1, v_a_2776_);
return v___x_2780_;
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v_a_2786_; lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v___x_2781_ = lean_unsigned_to_nat(1u);
v___x_2782_ = l_Lean_Syntax_getArg(v_x_2774_, v___x_2781_);
v___x_2783_ = lean_unsigned_to_nat(3u);
v___x_2784_ = l_Lean_Syntax_getArg(v_x_2774_, v___x_2783_);
lean_dec(v_x_2774_);
v___x_2785_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v___x_2782_, v___x_2784_, v_a_2775_, v_a_2776_);
lean_dec(v___x_2782_);
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_a_2787_ = lean_ctor_get(v___x_2785_, 1);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2785_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2786_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object* v_x_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(v_x_2795_, v_a_2796_, v_a_2797_);
lean_dec_ref(v_a_2796_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object* v_inst_2799_, lean_object* v_inst_2800_, lean_object* v_inst_2801_, lean_object* v_inst_2802_, lean_object* v_always_2803_, lean_object* v_inst_2804_, lean_object* v_cls_2805_, uint8_t v_collapsed_2806_, lean_object* v_tag_2807_, lean_object* v_opts_2808_, uint8_t v_clsEnabled_2809_, lean_object* v_oldTraces_2810_, lean_object* v_ref_2811_, lean_object* v_msg_2812_, lean_object* v_resStartStop_2813_){
_start:
{
lean_object* v___x_2814_; lean_object* v_snd_2815_; lean_object* v_fst_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2882_; 
v___x_2814_ = l_Lean_KVMap_instValueBool;
v_snd_2815_ = lean_ctor_get(v_resStartStop_2813_, 1);
v_fst_2816_ = lean_ctor_get(v_resStartStop_2813_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_resStartStop_2813_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2818_ = v_resStartStop_2813_;
v_isShared_2819_ = v_isSharedCheck_2882_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_snd_2815_);
lean_inc(v_fst_2816_);
lean_dec(v_resStartStop_2813_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2882_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_fst_2820_; lean_object* v_snd_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2881_; 
v_fst_2820_ = lean_ctor_get(v_snd_2815_, 0);
v_snd_2821_ = lean_ctor_get(v_snd_2815_, 1);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_snd_2815_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2823_ = v_snd_2815_;
v_isShared_2824_ = v_isSharedCheck_2881_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_snd_2821_);
lean_inc(v_fst_2820_);
lean_dec(v_snd_2815_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2881_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___f_2825_; lean_object* v___f_2826_; lean_object* v___y_2828_; lean_object* v_data_2829_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___y_2855_; double v___y_2861_; uint8_t v___x_2866_; 
lean_inc_ref(v_oldTraces_2810_);
v___f_2825_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2825_, 0, v_oldTraces_2810_);
lean_inc(v_fst_2816_);
lean_inc_ref(v_inst_2799_);
v___f_2826_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2826_, 0, v_always_2803_);
lean_closure_set(v___f_2826_, 1, v_inst_2799_);
lean_closure_set(v___f_2826_, 2, v_fst_2816_);
v___x_2833_ = l_Lean_trace_profiler;
v___x_2834_ = l_Lean_Option_get___redArg(v___x_2814_, v_opts_2808_, v___x_2833_);
v___x_2866_ = lean_unbox(v___x_2834_);
if (v___x_2866_ == 0)
{
uint8_t v___x_2867_; 
v___x_2867_ = lean_unbox(v___x_2834_);
v___y_2855_ = v___x_2867_;
goto v___jp_2854_;
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2868_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2869_ = l_Lean_Option_get___redArg(v___x_2814_, v_opts_2808_, v___x_2868_);
v___x_2870_ = lean_unbox(v___x_2869_);
lean_dec(v___x_2869_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; double v___x_2874_; double v___x_2875_; double v___x_2876_; 
v___x_2871_ = l_Lean_KVMap_instValueNat;
v___x_2872_ = l_Lean_trace_profiler_threshold;
v___x_2873_ = l_Lean_Option_get___redArg(v___x_2871_, v_opts_2808_, v___x_2872_);
v___x_2874_ = lean_float_of_nat(v___x_2873_);
v___x_2875_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_2876_ = lean_float_div(v___x_2874_, v___x_2875_);
v___y_2861_ = v___x_2876_;
goto v___jp_2860_;
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; double v___x_2880_; 
v___x_2877_ = l_Lean_KVMap_instValueNat;
v___x_2878_ = l_Lean_trace_profiler_threshold;
v___x_2879_ = l_Lean_Option_get___redArg(v___x_2877_, v_opts_2808_, v___x_2878_);
v___x_2880_ = lean_float_of_nat(v___x_2879_);
v___y_2861_ = v___x_2880_;
goto v___jp_2860_;
}
}
v___jp_2827_:
{
lean_object* v_toBind_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_toBind_2830_ = lean_ctor_get(v_inst_2799_, 1);
lean_inc(v_toBind_2830_);
v___x_2831_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_2799_, v_inst_2800_, v_inst_2801_, v_inst_2802_, v_oldTraces_2810_, v_data_2829_, v_ref_2811_, v___y_2828_);
v___x_2832_ = lean_apply_4(v_toBind_2830_, lean_box(0), lean_box(0), v___x_2831_, v___f_2826_);
return v___x_2832_;
}
v___jp_2835_:
{
lean_object* v_result_2836_; uint8_t v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
v_result_2836_ = lean_apply_1(v_inst_2804_, v_fst_2816_);
v___x_2837_ = lean_unbox(v_result_2836_);
v___x_2838_ = l_Lean_TraceResult_toEmoji(v___x_2837_);
v___x_2839_ = l_Lean_stringToMessageData(v___x_2838_);
v___x_2840_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
if (v_isShared_2824_ == 0)
{
lean_ctor_set_tag(v___x_2823_, 7);
lean_ctor_set(v___x_2823_, 1, v___x_2840_);
lean_ctor_set(v___x_2823_, 0, v___x_2839_);
v___x_2842_ = v___x_2823_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v_msg_2844_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set_tag(v___x_2818_, 7);
lean_ctor_set(v___x_2818_, 1, v_msg_2812_);
lean_ctor_set(v___x_2818_, 0, v___x_2842_);
v_msg_2844_ = v___x_2818_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_msg_2812_);
v_msg_2844_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
lean_object* v___x_2845_; double v___x_2846_; lean_object* v_data_2847_; uint8_t v___x_2848_; 
v___x_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2845_, 0, v_result_2836_);
v___x_2846_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_2807_);
lean_inc_ref(v___x_2845_);
lean_inc(v_cls_2805_);
v_data_2847_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2847_, 0, v_cls_2805_);
lean_ctor_set(v_data_2847_, 1, v___x_2845_);
lean_ctor_set(v_data_2847_, 2, v_tag_2807_);
lean_ctor_set_float(v_data_2847_, sizeof(void*)*3, v___x_2846_);
lean_ctor_set_float(v_data_2847_, sizeof(void*)*3 + 8, v___x_2846_);
lean_ctor_set_uint8(v_data_2847_, sizeof(void*)*3 + 16, v_collapsed_2806_);
v___x_2848_ = lean_unbox(v___x_2834_);
lean_dec(v___x_2834_);
if (v___x_2848_ == 0)
{
lean_dec_ref(v___x_2845_);
lean_dec(v_snd_2821_);
lean_dec(v_fst_2820_);
lean_dec_ref(v_tag_2807_);
lean_dec(v_cls_2805_);
v___y_2828_ = v_msg_2844_;
v_data_2829_ = v_data_2847_;
goto v___jp_2827_;
}
else
{
lean_object* v_data_2849_; double v___x_2850_; double v___x_2851_; 
lean_dec_ref(v_data_2847_);
v_data_2849_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2849_, 0, v_cls_2805_);
lean_ctor_set(v_data_2849_, 1, v___x_2845_);
lean_ctor_set(v_data_2849_, 2, v_tag_2807_);
v___x_2850_ = lean_unbox_float(v_fst_2820_);
lean_dec(v_fst_2820_);
lean_ctor_set_float(v_data_2849_, sizeof(void*)*3, v___x_2850_);
v___x_2851_ = lean_unbox_float(v_snd_2821_);
lean_dec(v_snd_2821_);
lean_ctor_set_float(v_data_2849_, sizeof(void*)*3 + 8, v___x_2851_);
lean_ctor_set_uint8(v_data_2849_, sizeof(void*)*3 + 16, v_collapsed_2806_);
v___y_2828_ = v_msg_2844_;
v_data_2829_ = v_data_2849_;
goto v___jp_2827_;
}
}
}
}
v___jp_2854_:
{
if (v_clsEnabled_2809_ == 0)
{
if (v___y_2855_ == 0)
{
lean_object* v_toBind_2856_; lean_object* v_modifyTraceState_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_dec(v___x_2834_);
lean_del_object(v___x_2823_);
lean_dec(v_snd_2821_);
lean_dec(v_fst_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_fst_2816_);
lean_dec_ref(v_msg_2812_);
lean_dec(v_ref_2811_);
lean_dec_ref(v_oldTraces_2810_);
lean_dec_ref(v_tag_2807_);
lean_dec(v_cls_2805_);
lean_dec_ref(v_inst_2804_);
lean_dec(v_inst_2802_);
lean_dec_ref(v_inst_2801_);
v_toBind_2856_ = lean_ctor_get(v_inst_2799_, 1);
lean_inc(v_toBind_2856_);
lean_dec_ref(v_inst_2799_);
v_modifyTraceState_2857_ = lean_ctor_get(v_inst_2800_, 0);
lean_inc(v_modifyTraceState_2857_);
lean_dec_ref(v_inst_2800_);
v___x_2858_ = lean_apply_1(v_modifyTraceState_2857_, v___f_2825_);
v___x_2859_ = lean_apply_4(v_toBind_2856_, lean_box(0), lean_box(0), v___x_2858_, v___f_2826_);
return v___x_2859_;
}
else
{
lean_dec_ref(v___f_2825_);
goto v___jp_2835_;
}
}
else
{
lean_dec_ref(v___f_2825_);
goto v___jp_2835_;
}
}
v___jp_2860_:
{
double v___x_2862_; double v___x_2863_; double v___x_2864_; uint8_t v___x_2865_; 
v___x_2862_ = lean_unbox_float(v_snd_2821_);
v___x_2863_ = lean_unbox_float(v_fst_2820_);
v___x_2864_ = lean_float_sub(v___x_2862_, v___x_2863_);
v___x_2865_ = lean_float_decLt(v___y_2861_, v___x_2864_);
v___y_2855_ = v___x_2865_;
goto v___jp_2854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_inst_2885_, lean_object* v_inst_2886_, lean_object* v_always_2887_, lean_object* v_inst_2888_, lean_object* v_cls_2889_, lean_object* v_collapsed_2890_, lean_object* v_tag_2891_, lean_object* v_opts_2892_, lean_object* v_clsEnabled_2893_, lean_object* v_oldTraces_2894_, lean_object* v_ref_2895_, lean_object* v_msg_2896_, lean_object* v_resStartStop_2897_){
_start:
{
uint8_t v_collapsed_boxed_2898_; uint8_t v_clsEnabled_boxed_2899_; lean_object* v_res_2900_; 
v_collapsed_boxed_2898_ = lean_unbox(v_collapsed_2890_);
v_clsEnabled_boxed_2899_ = lean_unbox(v_clsEnabled_2893_);
v_res_2900_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2883_, v_inst_2884_, v_inst_2885_, v_inst_2886_, v_always_2887_, v_inst_2888_, v_cls_2889_, v_collapsed_boxed_2898_, v_tag_2891_, v_opts_2892_, v_clsEnabled_boxed_2899_, v_oldTraces_2894_, v_ref_2895_, v_msg_2896_, v_resStartStop_2897_);
lean_dec_ref(v_opts_2892_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object* v_00_u03b1_2901_, lean_object* v_m_2902_, lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_00_u03b5_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_always_2908_, lean_object* v_inst_2909_, lean_object* v_cls_2910_, uint8_t v_collapsed_2911_, lean_object* v_tag_2912_, lean_object* v_opts_2913_, uint8_t v_clsEnabled_2914_, lean_object* v_oldTraces_2915_, lean_object* v_ref_2916_, lean_object* v_msg_2917_, lean_object* v_resStartStop_2918_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2903_, v_inst_2904_, v_inst_2906_, v_inst_2907_, v_always_2908_, v_inst_2909_, v_cls_2910_, v_collapsed_2911_, v_tag_2912_, v_opts_2913_, v_clsEnabled_2914_, v_oldTraces_2915_, v_ref_2916_, v_msg_2917_, v_resStartStop_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_2920_ = _args[0];
lean_object* v_m_2921_ = _args[1];
lean_object* v_inst_2922_ = _args[2];
lean_object* v_inst_2923_ = _args[3];
lean_object* v_00_u03b5_2924_ = _args[4];
lean_object* v_inst_2925_ = _args[5];
lean_object* v_inst_2926_ = _args[6];
lean_object* v_always_2927_ = _args[7];
lean_object* v_inst_2928_ = _args[8];
lean_object* v_cls_2929_ = _args[9];
lean_object* v_collapsed_2930_ = _args[10];
lean_object* v_tag_2931_ = _args[11];
lean_object* v_opts_2932_ = _args[12];
lean_object* v_clsEnabled_2933_ = _args[13];
lean_object* v_oldTraces_2934_ = _args[14];
lean_object* v_ref_2935_ = _args[15];
lean_object* v_msg_2936_ = _args[16];
lean_object* v_resStartStop_2937_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2938_; uint8_t v_clsEnabled_boxed_2939_; lean_object* v_res_2940_; 
v_collapsed_boxed_2938_ = lean_unbox(v_collapsed_2930_);
v_clsEnabled_boxed_2939_ = lean_unbox(v_clsEnabled_2933_);
v_res_2940_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(v_00_u03b1_2920_, v_m_2921_, v_inst_2922_, v_inst_2923_, v_00_u03b5_2924_, v_inst_2925_, v_inst_2926_, v_always_2927_, v_inst_2928_, v_cls_2929_, v_collapsed_boxed_2938_, v_tag_2931_, v_opts_2932_, v_clsEnabled_boxed_2939_, v_oldTraces_2934_, v_ref_2935_, v_msg_2936_, v_resStartStop_2937_);
lean_dec_ref(v_opts_2932_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object* v_inst_2941_, lean_object* v_____do__lift_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_apply_1(v_inst_2941_, v_____do__lift_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_inst_2947_, lean_object* v_always_2948_, lean_object* v_inst_2949_, lean_object* v_cls_2950_, uint8_t v_collapsed_2951_, lean_object* v_tag_2952_, lean_object* v_opts_2953_, uint8_t v_clsEnabled_2954_, lean_object* v_oldTraces_2955_, lean_object* v_ref_2956_, lean_object* v_msg_2957_, lean_object* v_resStartStop_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2944_, v_inst_2945_, v_inst_2946_, v_inst_2947_, v_always_2948_, v_inst_2949_, v_cls_2950_, v_collapsed_2951_, v_tag_2952_, v_opts_2953_, v_clsEnabled_2954_, v_oldTraces_2955_, v_ref_2956_, v_msg_2957_, v_resStartStop_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object* v_inst_2960_, lean_object* v_inst_2961_, lean_object* v_inst_2962_, lean_object* v_inst_2963_, lean_object* v_always_2964_, lean_object* v_inst_2965_, lean_object* v_cls_2966_, lean_object* v_collapsed_2967_, lean_object* v_tag_2968_, lean_object* v_opts_2969_, lean_object* v_clsEnabled_2970_, lean_object* v_oldTraces_2971_, lean_object* v_ref_2972_, lean_object* v_msg_2973_, lean_object* v_resStartStop_2974_){
_start:
{
uint8_t v_collapsed_boxed_2975_; uint8_t v_clsEnabled_boxed_2976_; lean_object* v_res_2977_; 
v_collapsed_boxed_2975_ = lean_unbox(v_collapsed_2967_);
v_clsEnabled_boxed_2976_ = lean_unbox(v_clsEnabled_2970_);
v_res_2977_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_2960_, v_inst_2961_, v_inst_2962_, v_inst_2963_, v_always_2964_, v_inst_2965_, v_cls_2966_, v_collapsed_boxed_2975_, v_tag_2968_, v_opts_2969_, v_clsEnabled_boxed_2976_, v_oldTraces_2971_, v_ref_2972_, v_msg_2973_, v_resStartStop_2974_);
lean_dec_ref(v_opts_2969_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object* v_always_2978_, lean_object* v_inst_2979_, lean_object* v_inst_2980_, lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_cls_2984_, uint8_t v_collapsed_2985_, lean_object* v_tag_2986_, lean_object* v_opts_2987_, uint8_t v_clsEnabled_2988_, lean_object* v_oldTraces_2989_, lean_object* v_ref_2990_, lean_object* v_toPure_2991_, lean_object* v_toBind_2992_, lean_object* v_k_2993_, lean_object* v_inst_2994_, lean_object* v_msg_2995_){
_start:
{
lean_object* v_tryCatch_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___f_2999_; lean_object* v___f_3000_; lean_object* v___f_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v_tryCatch_2996_ = lean_ctor_get(v_always_2978_, 1);
lean_inc(v_tryCatch_2996_);
v___x_2997_ = lean_box(v_collapsed_2985_);
v___x_2998_ = lean_box(v_clsEnabled_2988_);
lean_inc_ref(v_opts_2987_);
v___f_2999_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__1___boxed), 15, 14);
lean_closure_set(v___f_2999_, 0, v_inst_2979_);
lean_closure_set(v___f_2999_, 1, v_inst_2980_);
lean_closure_set(v___f_2999_, 2, v_inst_2981_);
lean_closure_set(v___f_2999_, 3, v_inst_2982_);
lean_closure_set(v___f_2999_, 4, v_always_2978_);
lean_closure_set(v___f_2999_, 5, v_inst_2983_);
lean_closure_set(v___f_2999_, 6, v_cls_2984_);
lean_closure_set(v___f_2999_, 7, v___x_2997_);
lean_closure_set(v___f_2999_, 8, v_tag_2986_);
lean_closure_set(v___f_2999_, 9, v_opts_2987_);
lean_closure_set(v___f_2999_, 10, v___x_2998_);
lean_closure_set(v___f_2999_, 11, v_oldTraces_2989_);
lean_closure_set(v___f_2999_, 12, v_ref_2990_);
lean_closure_set(v___f_2999_, 13, v_msg_2995_);
lean_inc_n(v_toPure_2991_, 2);
v___f_3000_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3000_, 0, v_toPure_2991_);
v___f_3001_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3001_, 0, v_toPure_2991_);
lean_inc(v_toBind_2992_);
v___x_3002_ = lean_apply_4(v_toBind_2992_, lean_box(0), lean_box(0), v_k_2993_, v___f_3001_);
v___x_3003_ = lean_apply_3(v_tryCatch_2996_, lean_box(0), v___x_3002_, v___f_3000_);
v___x_3004_ = l_Lean_KVMap_instValueBool;
v___x_3005_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3006_ = l_Lean_Option_get___redArg(v___x_3004_, v_opts_2987_, v___x_3005_);
lean_dec_ref(v_opts_2987_);
v___x_3007_ = lean_unbox(v___x_3006_);
lean_dec(v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___f_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3008_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_3009_ = lean_apply_2(v_inst_2994_, lean_box(0), v___x_3008_);
lean_inc(v___x_3009_);
lean_inc_n(v_toBind_2992_, 2);
v___f_3010_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3010_, 0, v_toPure_2991_);
lean_closure_set(v___f_3010_, 1, v_toBind_2992_);
lean_closure_set(v___f_3010_, 2, v___x_3009_);
lean_closure_set(v___f_3010_, 3, v___x_3003_);
v___x_3011_ = lean_apply_4(v_toBind_2992_, lean_box(0), lean_box(0), v___x_3009_, v___f_3010_);
v___x_3012_ = lean_apply_4(v_toBind_2992_, lean_box(0), lean_box(0), v___x_3011_, v___f_2999_);
return v___x_3012_;
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___f_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3013_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_3014_ = lean_apply_2(v_inst_2994_, lean_box(0), v___x_3013_);
lean_inc(v___x_3014_);
lean_inc_n(v_toBind_2992_, 2);
v___f_3015_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_3015_, 0, v_toPure_2991_);
lean_closure_set(v___f_3015_, 1, v_toBind_2992_);
lean_closure_set(v___f_3015_, 2, v___x_3014_);
lean_closure_set(v___f_3015_, 3, v___x_3003_);
v___x_3016_ = lean_apply_4(v_toBind_2992_, lean_box(0), lean_box(0), v___x_3014_, v___f_3015_);
v___x_3017_ = lean_apply_4(v_toBind_2992_, lean_box(0), lean_box(0), v___x_3016_, v___f_2999_);
return v___x_3017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_3018_ = _args[0];
lean_object* v_inst_3019_ = _args[1];
lean_object* v_inst_3020_ = _args[2];
lean_object* v_inst_3021_ = _args[3];
lean_object* v_inst_3022_ = _args[4];
lean_object* v_inst_3023_ = _args[5];
lean_object* v_cls_3024_ = _args[6];
lean_object* v_collapsed_3025_ = _args[7];
lean_object* v_tag_3026_ = _args[8];
lean_object* v_opts_3027_ = _args[9];
lean_object* v_clsEnabled_3028_ = _args[10];
lean_object* v_oldTraces_3029_ = _args[11];
lean_object* v_ref_3030_ = _args[12];
lean_object* v_toPure_3031_ = _args[13];
lean_object* v_toBind_3032_ = _args[14];
lean_object* v_k_3033_ = _args[15];
lean_object* v_inst_3034_ = _args[16];
lean_object* v_msg_3035_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3036_; uint8_t v_clsEnabled_boxed_3037_; lean_object* v_res_3038_; 
v_collapsed_boxed_3036_ = lean_unbox(v_collapsed_3025_);
v_clsEnabled_boxed_3037_ = lean_unbox(v_clsEnabled_3028_);
v_res_3038_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_always_3018_, v_inst_3019_, v_inst_3020_, v_inst_3021_, v_inst_3022_, v_inst_3023_, v_cls_3024_, v_collapsed_boxed_3036_, v_tag_3026_, v_opts_3027_, v_clsEnabled_boxed_3037_, v_oldTraces_3029_, v_ref_3030_, v_toPure_3031_, v_toBind_3032_, v_k_3033_, v_inst_3034_, v_msg_3035_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object* v_always_3039_, lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_inst_3042_, lean_object* v_inst_3043_, lean_object* v_inst_3044_, lean_object* v_cls_3045_, uint8_t v_collapsed_3046_, lean_object* v_tag_3047_, lean_object* v_opts_3048_, uint8_t v_clsEnabled_3049_, lean_object* v_oldTraces_3050_, lean_object* v_toPure_3051_, lean_object* v_toBind_3052_, lean_object* v_k_3053_, lean_object* v_inst_3054_, lean_object* v_msg_3055_, lean_object* v___f_3056_, lean_object* v_withRef_3057_, lean_object* v_getRef_3058_, lean_object* v_ref_3059_){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___f_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___f_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3060_ = lean_box(v_collapsed_3046_);
v___x_3061_ = lean_box(v_clsEnabled_3049_);
lean_inc_n(v_toBind_3052_, 3);
lean_inc(v_ref_3059_);
v___f_3062_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__10___boxed), 18, 17);
lean_closure_set(v___f_3062_, 0, v_always_3039_);
lean_closure_set(v___f_3062_, 1, v_inst_3040_);
lean_closure_set(v___f_3062_, 2, v_inst_3041_);
lean_closure_set(v___f_3062_, 3, v_inst_3042_);
lean_closure_set(v___f_3062_, 4, v_inst_3043_);
lean_closure_set(v___f_3062_, 5, v_inst_3044_);
lean_closure_set(v___f_3062_, 6, v_cls_3045_);
lean_closure_set(v___f_3062_, 7, v___x_3060_);
lean_closure_set(v___f_3062_, 8, v_tag_3047_);
lean_closure_set(v___f_3062_, 9, v_opts_3048_);
lean_closure_set(v___f_3062_, 10, v___x_3061_);
lean_closure_set(v___f_3062_, 11, v_oldTraces_3050_);
lean_closure_set(v___f_3062_, 12, v_ref_3059_);
lean_closure_set(v___f_3062_, 13, v_toPure_3051_);
lean_closure_set(v___f_3062_, 14, v_toBind_3052_);
lean_closure_set(v___f_3062_, 15, v_k_3053_);
lean_closure_set(v___f_3062_, 16, v_inst_3054_);
v___x_3063_ = lean_box(0);
v___x_3064_ = lean_apply_1(v_msg_3055_, v___x_3063_);
v___x_3065_ = lean_apply_4(v_toBind_3052_, lean_box(0), lean_box(0), v___x_3064_, v___f_3056_);
v___f_3066_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3066_, 0, v_ref_3059_);
lean_closure_set(v___f_3066_, 1, v_withRef_3057_);
lean_closure_set(v___f_3066_, 2, v___x_3065_);
v___x_3067_ = lean_apply_4(v_toBind_3052_, lean_box(0), lean_box(0), v_getRef_3058_, v___f_3066_);
v___x_3068_ = lean_apply_4(v_toBind_3052_, lean_box(0), lean_box(0), v___x_3067_, v___f_3062_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_3069_ = _args[0];
lean_object* v_inst_3070_ = _args[1];
lean_object* v_inst_3071_ = _args[2];
lean_object* v_inst_3072_ = _args[3];
lean_object* v_inst_3073_ = _args[4];
lean_object* v_inst_3074_ = _args[5];
lean_object* v_cls_3075_ = _args[6];
lean_object* v_collapsed_3076_ = _args[7];
lean_object* v_tag_3077_ = _args[8];
lean_object* v_opts_3078_ = _args[9];
lean_object* v_clsEnabled_3079_ = _args[10];
lean_object* v_oldTraces_3080_ = _args[11];
lean_object* v_toPure_3081_ = _args[12];
lean_object* v_toBind_3082_ = _args[13];
lean_object* v_k_3083_ = _args[14];
lean_object* v_inst_3084_ = _args[15];
lean_object* v_msg_3085_ = _args[16];
lean_object* v___f_3086_ = _args[17];
lean_object* v_withRef_3087_ = _args[18];
lean_object* v_getRef_3088_ = _args[19];
lean_object* v_ref_3089_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_3090_; uint8_t v_clsEnabled_boxed_3091_; lean_object* v_res_3092_; 
v_collapsed_boxed_3090_ = lean_unbox(v_collapsed_3076_);
v_clsEnabled_boxed_3091_ = lean_unbox(v_clsEnabled_3079_);
v_res_3092_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_always_3069_, v_inst_3070_, v_inst_3071_, v_inst_3072_, v_inst_3073_, v_inst_3074_, v_cls_3075_, v_collapsed_boxed_3090_, v_tag_3077_, v_opts_3078_, v_clsEnabled_boxed_3091_, v_oldTraces_3080_, v_toPure_3081_, v_toBind_3082_, v_k_3083_, v_inst_3084_, v_msg_3085_, v___f_3086_, v_withRef_3087_, v_getRef_3088_, v_ref_3089_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object* v_inst_3093_, lean_object* v_always_3094_, lean_object* v_inst_3095_, lean_object* v_inst_3096_, lean_object* v_inst_3097_, lean_object* v_inst_3098_, lean_object* v_cls_3099_, uint8_t v_collapsed_3100_, lean_object* v_tag_3101_, lean_object* v_opts_3102_, uint8_t v_clsEnabled_3103_, lean_object* v_toPure_3104_, lean_object* v_toBind_3105_, lean_object* v_k_3106_, lean_object* v_inst_3107_, lean_object* v_msg_3108_, lean_object* v___f_3109_, lean_object* v_oldTraces_3110_){
_start:
{
lean_object* v_getRef_3111_; lean_object* v_withRef_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___f_3115_; lean_object* v___x_3116_; 
v_getRef_3111_ = lean_ctor_get(v_inst_3093_, 0);
lean_inc_n(v_getRef_3111_, 2);
v_withRef_3112_ = lean_ctor_get(v_inst_3093_, 1);
lean_inc(v_withRef_3112_);
v___x_3113_ = lean_box(v_collapsed_3100_);
v___x_3114_ = lean_box(v_clsEnabled_3103_);
lean_inc(v_toBind_3105_);
v___f_3115_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__3___boxed), 21, 20);
lean_closure_set(v___f_3115_, 0, v_always_3094_);
lean_closure_set(v___f_3115_, 1, v_inst_3095_);
lean_closure_set(v___f_3115_, 2, v_inst_3096_);
lean_closure_set(v___f_3115_, 3, v_inst_3093_);
lean_closure_set(v___f_3115_, 4, v_inst_3097_);
lean_closure_set(v___f_3115_, 5, v_inst_3098_);
lean_closure_set(v___f_3115_, 6, v_cls_3099_);
lean_closure_set(v___f_3115_, 7, v___x_3113_);
lean_closure_set(v___f_3115_, 8, v_tag_3101_);
lean_closure_set(v___f_3115_, 9, v_opts_3102_);
lean_closure_set(v___f_3115_, 10, v___x_3114_);
lean_closure_set(v___f_3115_, 11, v_oldTraces_3110_);
lean_closure_set(v___f_3115_, 12, v_toPure_3104_);
lean_closure_set(v___f_3115_, 13, v_toBind_3105_);
lean_closure_set(v___f_3115_, 14, v_k_3106_);
lean_closure_set(v___f_3115_, 15, v_inst_3107_);
lean_closure_set(v___f_3115_, 16, v_msg_3108_);
lean_closure_set(v___f_3115_, 17, v___f_3109_);
lean_closure_set(v___f_3115_, 18, v_withRef_3112_);
lean_closure_set(v___f_3115_, 19, v_getRef_3111_);
v___x_3116_ = lean_apply_4(v_toBind_3105_, lean_box(0), lean_box(0), v_getRef_3111_, v___f_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_3117_ = _args[0];
lean_object* v_always_3118_ = _args[1];
lean_object* v_inst_3119_ = _args[2];
lean_object* v_inst_3120_ = _args[3];
lean_object* v_inst_3121_ = _args[4];
lean_object* v_inst_3122_ = _args[5];
lean_object* v_cls_3123_ = _args[6];
lean_object* v_collapsed_3124_ = _args[7];
lean_object* v_tag_3125_ = _args[8];
lean_object* v_opts_3126_ = _args[9];
lean_object* v_clsEnabled_3127_ = _args[10];
lean_object* v_toPure_3128_ = _args[11];
lean_object* v_toBind_3129_ = _args[12];
lean_object* v_k_3130_ = _args[13];
lean_object* v_inst_3131_ = _args[14];
lean_object* v_msg_3132_ = _args[15];
lean_object* v___f_3133_ = _args[16];
lean_object* v_oldTraces_3134_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3135_; uint8_t v_clsEnabled_boxed_3136_; lean_object* v_res_3137_; 
v_collapsed_boxed_3135_ = lean_unbox(v_collapsed_3124_);
v_clsEnabled_boxed_3136_ = lean_unbox(v_clsEnabled_3127_);
v_res_3137_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3117_, v_always_3118_, v_inst_3119_, v_inst_3120_, v_inst_3121_, v_inst_3122_, v_cls_3123_, v_collapsed_boxed_3135_, v_tag_3125_, v_opts_3126_, v_clsEnabled_boxed_3136_, v_toPure_3128_, v_toBind_3129_, v_k_3130_, v_inst_3131_, v_msg_3132_, v___f_3133_, v_oldTraces_3134_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object* v_inst_3138_, lean_object* v_always_3139_, lean_object* v_inst_3140_, lean_object* v_inst_3141_, lean_object* v_inst_3142_, lean_object* v_inst_3143_, lean_object* v_cls_3144_, uint8_t v_collapsed_3145_, lean_object* v_tag_3146_, lean_object* v_opts_3147_, lean_object* v_toPure_3148_, lean_object* v_toBind_3149_, lean_object* v_k_3150_, lean_object* v_inst_3151_, lean_object* v_msg_3152_, lean_object* v___f_3153_, uint8_t v_clsEnabled_3154_){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___f_3157_; 
v___x_3155_ = lean_box(v_collapsed_3145_);
v___x_3156_ = lean_box(v_clsEnabled_3154_);
lean_inc(v_k_3150_);
lean_inc(v_toBind_3149_);
lean_inc_ref(v_opts_3147_);
lean_inc_ref(v_inst_3141_);
lean_inc_ref(v_inst_3140_);
v___f_3157_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__2___boxed), 18, 17);
lean_closure_set(v___f_3157_, 0, v_inst_3138_);
lean_closure_set(v___f_3157_, 1, v_always_3139_);
lean_closure_set(v___f_3157_, 2, v_inst_3140_);
lean_closure_set(v___f_3157_, 3, v_inst_3141_);
lean_closure_set(v___f_3157_, 4, v_inst_3142_);
lean_closure_set(v___f_3157_, 5, v_inst_3143_);
lean_closure_set(v___f_3157_, 6, v_cls_3144_);
lean_closure_set(v___f_3157_, 7, v___x_3155_);
lean_closure_set(v___f_3157_, 8, v_tag_3146_);
lean_closure_set(v___f_3157_, 9, v_opts_3147_);
lean_closure_set(v___f_3157_, 10, v___x_3156_);
lean_closure_set(v___f_3157_, 11, v_toPure_3148_);
lean_closure_set(v___f_3157_, 12, v_toBind_3149_);
lean_closure_set(v___f_3157_, 13, v_k_3150_);
lean_closure_set(v___f_3157_, 14, v_inst_3151_);
lean_closure_set(v___f_3157_, 15, v_msg_3152_);
lean_closure_set(v___f_3157_, 16, v___f_3153_);
if (v_clsEnabled_3154_ == 0)
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3161_ = l_Lean_KVMap_instValueBool;
v___x_3162_ = l_Lean_trace_profiler;
v___x_3163_ = l_Lean_Option_get___redArg(v___x_3161_, v_opts_3147_, v___x_3162_);
lean_dec_ref(v_opts_3147_);
v___x_3164_ = lean_unbox(v___x_3163_);
lean_dec(v___x_3163_);
if (v___x_3164_ == 0)
{
lean_dec_ref(v___f_3157_);
lean_dec(v_toBind_3149_);
lean_dec_ref(v_inst_3141_);
lean_dec_ref(v_inst_3140_);
return v_k_3150_;
}
else
{
lean_dec(v_k_3150_);
goto v___jp_3158_;
}
}
else
{
lean_dec(v_k_3150_);
lean_dec_ref(v_opts_3147_);
goto v___jp_3158_;
}
v___jp_3158_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3140_, v_inst_3141_);
v___x_3160_ = lean_apply_4(v_toBind_3149_, lean_box(0), lean_box(0), v___x_3159_, v___f_3157_);
return v___x_3160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_3165_ = _args[0];
lean_object* v_always_3166_ = _args[1];
lean_object* v_inst_3167_ = _args[2];
lean_object* v_inst_3168_ = _args[3];
lean_object* v_inst_3169_ = _args[4];
lean_object* v_inst_3170_ = _args[5];
lean_object* v_cls_3171_ = _args[6];
lean_object* v_collapsed_3172_ = _args[7];
lean_object* v_tag_3173_ = _args[8];
lean_object* v_opts_3174_ = _args[9];
lean_object* v_toPure_3175_ = _args[10];
lean_object* v_toBind_3176_ = _args[11];
lean_object* v_k_3177_ = _args[12];
lean_object* v_inst_3178_ = _args[13];
lean_object* v_msg_3179_ = _args[14];
lean_object* v___f_3180_ = _args[15];
lean_object* v_clsEnabled_3181_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3182_; uint8_t v_clsEnabled_boxed_3183_; lean_object* v_res_3184_; 
v_collapsed_boxed_3182_ = lean_unbox(v_collapsed_3172_);
v_clsEnabled_boxed_3183_ = lean_unbox(v_clsEnabled_3181_);
v_res_3184_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3165_, v_always_3166_, v_inst_3167_, v_inst_3168_, v_inst_3169_, v_inst_3170_, v_cls_3171_, v_collapsed_boxed_3182_, v_tag_3173_, v_opts_3174_, v_toPure_3175_, v_toBind_3176_, v_k_3177_, v_inst_3178_, v_msg_3179_, v___f_3180_, v_clsEnabled_boxed_3183_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object* v_k_3185_, lean_object* v_inst_3186_, lean_object* v_toApplicative_3187_, lean_object* v_inst_3188_, lean_object* v_always_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_cls_3193_, uint8_t v_collapsed_3194_, lean_object* v_tag_3195_, lean_object* v_toBind_3196_, lean_object* v_inst_3197_, lean_object* v_msg_3198_, lean_object* v___f_3199_, lean_object* v_inst_3200_, lean_object* v_opts_3201_){
_start:
{
uint8_t v_hasTrace_3202_; 
v_hasTrace_3202_ = lean_ctor_get_uint8(v_opts_3201_, sizeof(void*)*1);
if (v_hasTrace_3202_ == 0)
{
lean_dec_ref(v_opts_3201_);
lean_dec(v_inst_3200_);
lean_dec(v___f_3199_);
lean_dec(v_msg_3198_);
lean_dec(v_inst_3197_);
lean_dec(v_toBind_3196_);
lean_dec_ref(v_tag_3195_);
lean_dec(v_cls_3193_);
lean_dec_ref(v_inst_3192_);
lean_dec(v_inst_3191_);
lean_dec_ref(v_inst_3190_);
lean_dec_ref(v_always_3189_);
lean_dec_ref(v_inst_3188_);
lean_dec_ref(v_toApplicative_3187_);
lean_dec_ref(v_inst_3186_);
return v_k_3185_;
}
else
{
lean_object* v_getInheritedTraceOptions_3203_; lean_object* v_toPure_3204_; lean_object* v___x_3205_; lean_object* v___f_3206_; lean_object* v___f_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v_getInheritedTraceOptions_3203_ = lean_ctor_get(v_inst_3186_, 2);
lean_inc(v_getInheritedTraceOptions_3203_);
v_toPure_3204_ = lean_ctor_get(v_toApplicative_3187_, 1);
lean_inc_n(v_toPure_3204_, 2);
lean_dec_ref(v_toApplicative_3187_);
v___x_3205_ = lean_box(v_collapsed_3194_);
lean_inc_n(v_toBind_3196_, 3);
lean_inc(v_cls_3193_);
v___f_3206_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_3206_, 0, v_inst_3188_);
lean_closure_set(v___f_3206_, 1, v_always_3189_);
lean_closure_set(v___f_3206_, 2, v_inst_3190_);
lean_closure_set(v___f_3206_, 3, v_inst_3186_);
lean_closure_set(v___f_3206_, 4, v_inst_3191_);
lean_closure_set(v___f_3206_, 5, v_inst_3192_);
lean_closure_set(v___f_3206_, 6, v_cls_3193_);
lean_closure_set(v___f_3206_, 7, v___x_3205_);
lean_closure_set(v___f_3206_, 8, v_tag_3195_);
lean_closure_set(v___f_3206_, 9, v_opts_3201_);
lean_closure_set(v___f_3206_, 10, v_toPure_3204_);
lean_closure_set(v___f_3206_, 11, v_toBind_3196_);
lean_closure_set(v___f_3206_, 12, v_k_3185_);
lean_closure_set(v___f_3206_, 13, v_inst_3197_);
lean_closure_set(v___f_3206_, 14, v_msg_3198_);
lean_closure_set(v___f_3206_, 15, v___f_3199_);
v___f_3207_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3207_, 0, v_toPure_3204_);
lean_closure_set(v___f_3207_, 1, v_cls_3193_);
lean_closure_set(v___f_3207_, 2, v_toBind_3196_);
lean_closure_set(v___f_3207_, 3, v_inst_3200_);
v___x_3208_ = lean_apply_4(v_toBind_3196_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3203_, v___f_3207_);
v___x_3209_ = lean_apply_4(v_toBind_3196_, lean_box(0), lean_box(0), v___x_3208_, v___f_3206_);
return v___x_3209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_k_3210_ = _args[0];
lean_object* v_inst_3211_ = _args[1];
lean_object* v_toApplicative_3212_ = _args[2];
lean_object* v_inst_3213_ = _args[3];
lean_object* v_always_3214_ = _args[4];
lean_object* v_inst_3215_ = _args[5];
lean_object* v_inst_3216_ = _args[6];
lean_object* v_inst_3217_ = _args[7];
lean_object* v_cls_3218_ = _args[8];
lean_object* v_collapsed_3219_ = _args[9];
lean_object* v_tag_3220_ = _args[10];
lean_object* v_toBind_3221_ = _args[11];
lean_object* v_inst_3222_ = _args[12];
lean_object* v_msg_3223_ = _args[13];
lean_object* v___f_3224_ = _args[14];
lean_object* v_inst_3225_ = _args[15];
lean_object* v_opts_3226_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3227_; lean_object* v_res_3228_; 
v_collapsed_boxed_3227_ = lean_unbox(v_collapsed_3219_);
v_res_3228_ = l_Lean_withTraceNodeBefore___redArg___lam__7(v_k_3210_, v_inst_3211_, v_toApplicative_3212_, v_inst_3213_, v_always_3214_, v_inst_3215_, v_inst_3216_, v_inst_3217_, v_cls_3218_, v_collapsed_boxed_3227_, v_tag_3220_, v_toBind_3221_, v_inst_3222_, v_msg_3223_, v___f_3224_, v_inst_3225_, v_opts_3226_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object* v_inst_3229_, lean_object* v_inst_3230_, lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_always_3234_, lean_object* v_inst_3235_, lean_object* v_inst_3236_, lean_object* v_cls_3237_, lean_object* v_msg_3238_, lean_object* v_k_3239_, uint8_t v_collapsed_3240_, lean_object* v_tag_3241_){
_start:
{
lean_object* v_toApplicative_3242_; lean_object* v_toBind_3243_; lean_object* v___f_3244_; lean_object* v___x_3245_; lean_object* v___f_3246_; lean_object* v___x_3247_; 
v_toApplicative_3242_ = lean_ctor_get(v_inst_3229_, 0);
lean_inc_ref(v_toApplicative_3242_);
v_toBind_3243_ = lean_ctor_get(v_inst_3229_, 1);
lean_inc_n(v_toBind_3243_, 2);
lean_inc(v_inst_3232_);
v___f_3244_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3244_, 0, v_inst_3232_);
v___x_3245_ = lean_box(v_collapsed_3240_);
lean_inc(v_inst_3233_);
v___f_3246_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3246_, 0, v_k_3239_);
lean_closure_set(v___f_3246_, 1, v_inst_3230_);
lean_closure_set(v___f_3246_, 2, v_toApplicative_3242_);
lean_closure_set(v___f_3246_, 3, v_inst_3231_);
lean_closure_set(v___f_3246_, 4, v_always_3234_);
lean_closure_set(v___f_3246_, 5, v_inst_3229_);
lean_closure_set(v___f_3246_, 6, v_inst_3232_);
lean_closure_set(v___f_3246_, 7, v_inst_3236_);
lean_closure_set(v___f_3246_, 8, v_cls_3237_);
lean_closure_set(v___f_3246_, 9, v___x_3245_);
lean_closure_set(v___f_3246_, 10, v_tag_3241_);
lean_closure_set(v___f_3246_, 11, v_toBind_3243_);
lean_closure_set(v___f_3246_, 12, v_inst_3235_);
lean_closure_set(v___f_3246_, 13, v_msg_3238_);
lean_closure_set(v___f_3246_, 14, v___f_3244_);
lean_closure_set(v___f_3246_, 15, v_inst_3233_);
v___x_3247_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v_inst_3233_, v___f_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_always_3253_, lean_object* v_inst_3254_, lean_object* v_inst_3255_, lean_object* v_cls_3256_, lean_object* v_msg_3257_, lean_object* v_k_3258_, lean_object* v_collapsed_3259_, lean_object* v_tag_3260_){
_start:
{
uint8_t v_collapsed_boxed_3261_; lean_object* v_res_3262_; 
v_collapsed_boxed_3261_ = lean_unbox(v_collapsed_3259_);
v_res_3262_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3248_, v_inst_3249_, v_inst_3250_, v_inst_3251_, v_inst_3252_, v_always_3253_, v_inst_3254_, v_inst_3255_, v_cls_3256_, v_msg_3257_, v_k_3258_, v_collapsed_boxed_3261_, v_tag_3260_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object* v_00_u03b1_3263_, lean_object* v_m_3264_, lean_object* v_inst_3265_, lean_object* v_inst_3266_, lean_object* v_00_u03b5_3267_, lean_object* v_inst_3268_, lean_object* v_inst_3269_, lean_object* v_inst_3270_, lean_object* v_always_3271_, lean_object* v_inst_3272_, lean_object* v_inst_3273_, lean_object* v_cls_3274_, lean_object* v_msg_3275_, lean_object* v_k_3276_, uint8_t v_collapsed_3277_, lean_object* v_tag_3278_){
_start:
{
lean_object* v_toApplicative_3279_; lean_object* v_toBind_3280_; lean_object* v___f_3281_; lean_object* v___x_3282_; lean_object* v___f_3283_; lean_object* v___x_3284_; 
v_toApplicative_3279_ = lean_ctor_get(v_inst_3265_, 0);
lean_inc_ref(v_toApplicative_3279_);
v_toBind_3280_ = lean_ctor_get(v_inst_3265_, 1);
lean_inc_n(v_toBind_3280_, 2);
lean_inc(v_inst_3269_);
v___f_3281_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3281_, 0, v_inst_3269_);
v___x_3282_ = lean_box(v_collapsed_3277_);
lean_inc(v_inst_3270_);
v___f_3283_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3283_, 0, v_k_3276_);
lean_closure_set(v___f_3283_, 1, v_inst_3266_);
lean_closure_set(v___f_3283_, 2, v_toApplicative_3279_);
lean_closure_set(v___f_3283_, 3, v_inst_3268_);
lean_closure_set(v___f_3283_, 4, v_always_3271_);
lean_closure_set(v___f_3283_, 5, v_inst_3265_);
lean_closure_set(v___f_3283_, 6, v_inst_3269_);
lean_closure_set(v___f_3283_, 7, v_inst_3273_);
lean_closure_set(v___f_3283_, 8, v_cls_3274_);
lean_closure_set(v___f_3283_, 9, v___x_3282_);
lean_closure_set(v___f_3283_, 10, v_tag_3278_);
lean_closure_set(v___f_3283_, 11, v_toBind_3280_);
lean_closure_set(v___f_3283_, 12, v_inst_3272_);
lean_closure_set(v___f_3283_, 13, v_msg_3275_);
lean_closure_set(v___f_3283_, 14, v___f_3281_);
lean_closure_set(v___f_3283_, 15, v_inst_3270_);
v___x_3284_ = lean_apply_4(v_toBind_3280_, lean_box(0), lean_box(0), v_inst_3270_, v___f_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object* v_00_u03b1_3285_, lean_object* v_m_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_00_u03b5_3289_, lean_object* v_inst_3290_, lean_object* v_inst_3291_, lean_object* v_inst_3292_, lean_object* v_always_3293_, lean_object* v_inst_3294_, lean_object* v_inst_3295_, lean_object* v_cls_3296_, lean_object* v_msg_3297_, lean_object* v_k_3298_, lean_object* v_collapsed_3299_, lean_object* v_tag_3300_){
_start:
{
uint8_t v_collapsed_boxed_3301_; lean_object* v_res_3302_; 
v_collapsed_boxed_3301_ = lean_unbox(v_collapsed_3299_);
v_res_3302_ = l_Lean_withTraceNodeBefore(v_00_u03b1_3285_, v_m_3286_, v_inst_3287_, v_inst_3288_, v_00_u03b5_3289_, v_inst_3290_, v_inst_3291_, v_inst_3292_, v_always_3293_, v_inst_3294_, v_inst_3295_, v_cls_3296_, v_msg_3297_, v_k_3298_, v_collapsed_boxed_3301_, v_tag_3300_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0(lean_object* v_toApplicative_3303_, lean_object* v_____s_3304_){
_start:
{
lean_object* v_toPure_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_toPure_3305_ = lean_ctor_get(v_toApplicative_3303_, 1);
lean_inc(v_toPure_3305_);
lean_dec_ref(v_toApplicative_3303_);
v___x_3306_ = lean_box(0);
v___x_3307_ = lean_apply_2(v_toPure_3305_, lean_box(0), v___x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__1(lean_object* v_x_3308_, lean_object* v_x_3309_){
_start:
{
lean_object* v_fst_3310_; lean_object* v_fst_3311_; lean_object* v_fst_3312_; lean_object* v_fst_3313_; uint8_t v___x_3314_; 
v_fst_3310_ = lean_ctor_get(v_x_3308_, 0);
v_fst_3311_ = lean_ctor_get(v_x_3309_, 0);
v_fst_3312_ = lean_ctor_get(v_fst_3310_, 0);
v_fst_3313_ = lean_ctor_get(v_fst_3311_, 0);
v___x_3314_ = lean_nat_dec_lt(v_fst_3312_, v_fst_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1___boxed(lean_object* v_x_3315_, lean_object* v_x_3316_){
_start:
{
uint8_t v_res_3317_; lean_object* v_r_3318_; 
v_res_3317_ = l_Lean_addTraceAsMessages___redArg___lam__1(v_x_3315_, v_x_3316_);
lean_dec_ref(v_x_3316_);
lean_dec_ref(v_x_3315_);
v_r_3318_ = lean_box(v_res_3317_);
return v_r_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object* v_x1_3319_, lean_object* v_x2_3320_, lean_object* v_x3_3321_){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3322_, 0, v_x2_3320_);
lean_ctor_set(v___x_3322_, 1, v_x3_3321_);
v___x_3323_ = lean_array_push(v_x1_3319_, v___x_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object* v_toApplicative_3324_, lean_object* v___x_3325_, lean_object* v_r_3326_){
_start:
{
lean_object* v_toPure_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v_toPure_3327_ = lean_ctor_get(v_toApplicative_3324_, 1);
lean_inc(v_toPure_3327_);
lean_dec_ref(v_toApplicative_3324_);
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3325_);
v___x_3329_ = lean_apply_2(v_toPure_3327_, lean_box(0), v___x_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object* v_____do__lift_3330_, lean_object* v___x_3331_, lean_object* v_fst_3332_, lean_object* v_snd_3333_, lean_object* v_logMessage_3334_, lean_object* v_toBind_3335_, lean_object* v___f_3336_, lean_object* v_____do__lift_3337_){
_start:
{
uint8_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3338_ = 0;
v___x_3339_ = l_Lean_Elab_mkMessageCore(v_____do__lift_3330_, v_____do__lift_3337_, v___x_3331_, v___x_3338_, v_fst_3332_, v_snd_3333_);
v___x_3340_ = lean_apply_1(v_logMessage_3334_, v___x_3339_);
v___x_3341_ = lean_apply_4(v_toBind_3335_, lean_box(0), lean_box(0), v___x_3340_, v___f_3336_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object* v_____do__lift_3342_, lean_object* v___x_3343_, lean_object* v_fst_3344_, lean_object* v_snd_3345_, lean_object* v_logMessage_3346_, lean_object* v_toBind_3347_, lean_object* v___f_3348_, lean_object* v_____do__lift_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_addTraceAsMessages___redArg___lam__4(v_____do__lift_3342_, v___x_3343_, v_fst_3344_, v_snd_3345_, v_logMessage_3346_, v_toBind_3347_, v___f_3348_, v_____do__lift_3349_);
lean_dec(v_snd_3345_);
lean_dec(v_fst_3344_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object* v___x_3351_, lean_object* v_fst_3352_, lean_object* v_snd_3353_, lean_object* v_logMessage_3354_, lean_object* v_toBind_3355_, lean_object* v___f_3356_, lean_object* v_toMonadFileMap_3357_, lean_object* v_____do__lift_3358_){
_start:
{
lean_object* v___f_3359_; lean_object* v___x_3360_; 
lean_inc(v_toBind_3355_);
v___f_3359_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_3359_, 0, v_____do__lift_3358_);
lean_closure_set(v___f_3359_, 1, v___x_3351_);
lean_closure_set(v___f_3359_, 2, v_fst_3352_);
lean_closure_set(v___f_3359_, 3, v_snd_3353_);
lean_closure_set(v___f_3359_, 4, v_logMessage_3354_);
lean_closure_set(v___f_3359_, 5, v_toBind_3355_);
lean_closure_set(v___f_3359_, 6, v___f_3356_);
v___x_3360_ = lean_apply_4(v_toBind_3355_, lean_box(0), lean_box(0), v_toMonadFileMap_3357_, v___f_3359_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object* v___x_3361_, uint8_t v___x_3362_, lean_object* v_inst_3363_, lean_object* v_toBind_3364_, lean_object* v___f_3365_, lean_object* v_a_3366_, lean_object* v_x_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_fst_3369_; lean_object* v_snd_3370_; lean_object* v_fst_3371_; lean_object* v_snd_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3392_; 
v_fst_3369_ = lean_ctor_get(v_a_3366_, 0);
lean_inc(v_fst_3369_);
v_snd_3370_ = lean_ctor_get(v_a_3366_, 1);
lean_inc(v_snd_3370_);
lean_dec_ref(v_a_3366_);
v_fst_3371_ = lean_ctor_get(v_fst_3369_, 0);
v_snd_3372_ = lean_ctor_get(v_fst_3369_, 1);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_fst_3369_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3374_ = v_fst_3369_;
v_isShared_3375_ = v_isSharedCheck_3392_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_snd_3372_);
lean_inc(v_fst_3371_);
lean_dec(v_fst_3369_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3392_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; double v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v_toMonadFileMap_3381_; lean_object* v_getFileName_3382_; lean_object* v_logMessage_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3376_ = lean_box(0);
v___x_3377_ = lean_box(0);
v___x_3378_ = lean_float_of_nat(v___x_3361_);
v___x_3379_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_3380_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3380_, 0, v___x_3376_);
lean_ctor_set(v___x_3380_, 1, v___x_3377_);
lean_ctor_set(v___x_3380_, 2, v___x_3379_);
lean_ctor_set_float(v___x_3380_, sizeof(void*)*3, v___x_3378_);
lean_ctor_set_float(v___x_3380_, sizeof(void*)*3 + 8, v___x_3378_);
lean_ctor_set_uint8(v___x_3380_, sizeof(void*)*3 + 16, v___x_3362_);
v_toMonadFileMap_3381_ = lean_ctor_get(v_inst_3363_, 0);
lean_inc(v_toMonadFileMap_3381_);
v_getFileName_3382_ = lean_ctor_get(v_inst_3363_, 2);
lean_inc(v_getFileName_3382_);
v_logMessage_3383_ = lean_ctor_get(v_inst_3363_, 4);
lean_inc(v_logMessage_3383_);
lean_dec_ref(v_inst_3363_);
v___x_3384_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_3385_ = l_Lean_MessageData_nil;
v___x_3386_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3380_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
lean_ctor_set(v___x_3386_, 2, v_snd_3370_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 8);
lean_ctor_set(v___x_3374_, 1, v___x_3386_);
lean_ctor_set(v___x_3374_, 0, v___x_3384_);
v___x_3388_ = v___x_3374_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___f_3389_; lean_object* v___x_3390_; 
lean_inc(v_toBind_3364_);
v___f_3389_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__5), 8, 7);
lean_closure_set(v___f_3389_, 0, v___x_3388_);
lean_closure_set(v___f_3389_, 1, v_fst_3371_);
lean_closure_set(v___f_3389_, 2, v_snd_3372_);
lean_closure_set(v___f_3389_, 3, v_logMessage_3383_);
lean_closure_set(v___f_3389_, 4, v_toBind_3364_);
lean_closure_set(v___f_3389_, 5, v___f_3365_);
lean_closure_set(v___f_3389_, 6, v_toMonadFileMap_3381_);
v___x_3390_ = lean_apply_4(v_toBind_3364_, lean_box(0), lean_box(0), v_getFileName_3382_, v___f_3389_);
return v___x_3390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object* v___x_3393_, lean_object* v___x_3394_, lean_object* v_inst_3395_, lean_object* v_toBind_3396_, lean_object* v___f_3397_, lean_object* v_a_3398_, lean_object* v_x_3399_, lean_object* v___y_3400_){
_start:
{
uint8_t v___x_1730__boxed_3401_; lean_object* v_res_3402_; 
v___x_1730__boxed_3401_ = lean_unbox(v___x_3394_);
v_res_3402_ = l_Lean_addTraceAsMessages___redArg___lam__6(v___x_3393_, v___x_1730__boxed_3401_, v_inst_3395_, v_toBind_3396_, v___f_3397_, v_a_3398_, v_x_3399_, v___y_3400_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object* v___x_3403_, lean_object* v___f_3404_, lean_object* v_acc_3405_, lean_object* v_l_3406_){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_3403_, v___f_3404_, v_acc_3405_, v_l_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object* v_toApplicative_3408_, uint8_t v___x_3409_, lean_object* v_inst_3410_, lean_object* v_toBind_3411_, lean_object* v_inst_3412_, lean_object* v___f_3413_, lean_object* v___f_3414_, lean_object* v___f_3415_, lean_object* v_____s_3416_){
_start:
{
lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3443_; lean_object* v_size_3450_; lean_object* v_buckets_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v_size_3450_ = lean_ctor_get(v_____s_3416_, 0);
lean_inc(v_size_3450_);
v_buckets_3451_ = lean_ctor_get(v_____s_3416_, 1);
lean_inc_ref(v_buckets_3451_);
lean_dec_ref(v_____s_3416_);
v___x_3452_ = lean_mk_empty_array_with_capacity(v_size_3450_);
lean_dec(v_size_3450_);
v___x_3453_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v___x_3454_ = lean_unsigned_to_nat(0u);
v___x_3455_ = lean_array_get_size(v_buckets_3451_);
v___x_3456_ = lean_nat_dec_lt(v___x_3454_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_dec_ref(v_buckets_3451_);
lean_dec_ref(v___f_3415_);
v___y_3443_ = v___x_3452_;
goto v___jp_3442_;
}
else
{
lean_object* v___f_3457_; uint8_t v___x_3458_; 
v___f_3457_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__7), 4, 2);
lean_closure_set(v___f_3457_, 0, v___x_3453_);
lean_closure_set(v___f_3457_, 1, v___f_3415_);
v___x_3458_ = lean_nat_dec_le(v___x_3455_, v___x_3455_);
if (v___x_3458_ == 0)
{
if (v___x_3456_ == 0)
{
lean_dec_ref(v___f_3457_);
lean_dec_ref(v_buckets_3451_);
v___y_3443_ = v___x_3452_;
goto v___jp_3442_;
}
else
{
size_t v___x_3459_; size_t v___x_3460_; lean_object* v___x_3461_; 
v___x_3459_ = ((size_t)0ULL);
v___x_3460_ = lean_usize_of_nat(v___x_3455_);
v___x_3461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3453_, v___f_3457_, v_buckets_3451_, v___x_3459_, v___x_3460_, v___x_3452_);
v___y_3443_ = v___x_3461_;
goto v___jp_3442_;
}
}
else
{
size_t v___x_3462_; size_t v___x_3463_; lean_object* v___x_3464_; 
v___x_3462_ = ((size_t)0ULL);
v___x_3463_ = lean_usize_of_nat(v___x_3455_);
v___x_3464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3453_, v___f_3457_, v_buckets_3451_, v___x_3462_, v___x_3463_, v___x_3452_);
v___y_3443_ = v___x_3464_;
goto v___jp_3442_;
}
}
v___jp_3417_:
{
lean_object* v___x_3420_; lean_object* v___f_3421_; lean_object* v___x_3422_; lean_object* v___f_3423_; size_t v_sz_3424_; size_t v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3420_ = lean_box(0);
v___f_3421_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3421_, 0, v_toApplicative_3408_);
lean_closure_set(v___f_3421_, 1, v___x_3420_);
v___x_3422_ = lean_box(v___x_3409_);
lean_inc(v_toBind_3411_);
v___f_3423_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__6___boxed), 8, 5);
lean_closure_set(v___f_3423_, 0, v___y_3418_);
lean_closure_set(v___f_3423_, 1, v___x_3422_);
lean_closure_set(v___f_3423_, 2, v_inst_3410_);
lean_closure_set(v___f_3423_, 3, v_toBind_3411_);
lean_closure_set(v___f_3423_, 4, v___f_3421_);
v_sz_3424_ = lean_array_size(v___y_3419_);
v___x_3425_ = ((size_t)0ULL);
v___x_3426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3412_, v___y_3419_, v___f_3423_, v_sz_3424_, v___x_3425_, v___x_3420_);
v___x_3427_ = lean_apply_4(v_toBind_3411_, lean_box(0), lean_box(0), v___x_3426_, v___f_3413_);
return v___x_3427_;
}
v___jp_3428_:
{
lean_object* v___x_3434_; 
v___x_3434_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_3414_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_3433_);
lean_dec(v___y_3430_);
v___y_3418_ = v___y_3429_;
v___y_3419_ = v___x_3434_;
goto v___jp_3417_;
}
v___jp_3435_:
{
uint8_t v___x_3441_; 
v___x_3441_ = lean_nat_dec_le(v___y_3440_, v___y_3439_);
if (v___x_3441_ == 0)
{
lean_dec(v___y_3439_);
lean_inc(v___y_3440_);
v___y_3429_ = v___y_3436_;
v___y_3430_ = v___y_3437_;
v___y_3431_ = v___y_3438_;
v___y_3432_ = v___y_3440_;
v___y_3433_ = v___y_3440_;
goto v___jp_3428_;
}
else
{
v___y_3429_ = v___y_3436_;
v___y_3430_ = v___y_3437_;
v___y_3431_ = v___y_3438_;
v___y_3432_ = v___y_3440_;
v___y_3433_ = v___y_3439_;
goto v___jp_3428_;
}
}
v___jp_3442_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v___x_3444_ = lean_unsigned_to_nat(0u);
v___x_3445_ = lean_array_get_size(v___y_3443_);
v___x_3446_ = lean_nat_dec_eq(v___x_3445_, v___x_3444_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v___x_3447_ = lean_unsigned_to_nat(1u);
v___x_3448_ = lean_nat_sub(v___x_3445_, v___x_3447_);
v___x_3449_ = lean_nat_dec_le(v___x_3444_, v___x_3448_);
if (v___x_3449_ == 0)
{
lean_inc(v___x_3448_);
v___y_3436_ = v___x_3444_;
v___y_3437_ = v___x_3445_;
v___y_3438_ = v___y_3443_;
v___y_3439_ = v___x_3448_;
v___y_3440_ = v___x_3448_;
goto v___jp_3435_;
}
else
{
v___y_3436_ = v___x_3444_;
v___y_3437_ = v___x_3445_;
v___y_3438_ = v___y_3443_;
v___y_3439_ = v___x_3448_;
v___y_3440_ = v___x_3444_;
goto v___jp_3435_;
}
}
else
{
lean_dec_ref(v___f_3414_);
v___y_3418_ = v___x_3444_;
v___y_3419_ = v___y_3443_;
goto v___jp_3417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object* v_toApplicative_3465_, lean_object* v___x_3466_, lean_object* v_inst_3467_, lean_object* v_toBind_3468_, lean_object* v_inst_3469_, lean_object* v___f_3470_, lean_object* v___f_3471_, lean_object* v___f_3472_, lean_object* v_____s_3473_){
_start:
{
uint8_t v___x_1818__boxed_3474_; lean_object* v_res_3475_; 
v___x_1818__boxed_3474_ = lean_unbox(v___x_3466_);
v_res_3475_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_toApplicative_3465_, v___x_1818__boxed_3474_, v_inst_3467_, v_toBind_3468_, v_inst_3469_, v___f_3470_, v___f_3471_, v___f_3472_, v_____s_3473_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object* v_traceElem_3476_, lean_object* v_toApplicative_3477_, lean_object* v___f_3478_, lean_object* v___f_3479_, lean_object* v_____s_3480_, uint8_t v___x_3481_, lean_object* v_____do__lift_3482_){
_start:
{
lean_object* v_ref_3483_; lean_object* v_msg_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3509_; 
v_ref_3483_ = lean_ctor_get(v_traceElem_3476_, 0);
v_msg_3484_ = lean_ctor_get(v_traceElem_3476_, 1);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_traceElem_3476_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3486_ = v_traceElem_3476_;
v_isShared_3487_ = v_isSharedCheck_3509_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_msg_3484_);
lean_inc(v_ref_3483_);
lean_dec(v_traceElem_3476_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3509_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v_ref_3501_; lean_object* v___y_3503_; lean_object* v___x_3506_; 
v_ref_3501_ = l_Lean_replaceRef(v_ref_3483_, v_____do__lift_3482_);
lean_dec(v_ref_3483_);
v___x_3506_ = l_Lean_Syntax_getPos_x3f(v_ref_3501_, v___x_3481_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v___x_3507_; 
v___x_3507_ = lean_unsigned_to_nat(0u);
v___y_3503_ = v___x_3507_;
goto v___jp_3502_;
}
else
{
lean_object* v_val_3508_; 
v_val_3508_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_val_3508_);
lean_dec_ref(v___x_3506_);
v___y_3503_ = v_val_3508_;
goto v___jp_3502_;
}
v___jp_3488_:
{
lean_object* v_toPure_3491_; lean_object* v___x_3493_; 
v_toPure_3491_ = lean_ctor_get(v_toApplicative_3477_, 1);
lean_inc(v_toPure_3491_);
lean_dec_ref(v_toApplicative_3477_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 1, v___y_3490_);
lean_ctor_set(v___x_3486_, 0, v___y_3489_);
v___x_3493_ = v___x_3486_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___y_3489_);
lean_ctor_set(v_reuseFailAlloc_3500_, 1, v___y_3490_);
v___x_3493_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v_pos2traces_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3494_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
lean_inc_ref(v___x_3493_);
lean_inc_ref(v___f_3479_);
lean_inc_ref(v___f_3478_);
v___x_3495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_3478_, v___f_3479_, v_____s_3480_, v___x_3493_, v___x_3494_);
v___x_3496_ = lean_array_push(v___x_3495_, v_msg_3484_);
v_pos2traces_3497_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3478_, v___f_3479_, v_____s_3480_, v___x_3493_, v___x_3496_);
v___x_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3498_, 0, v_pos2traces_3497_);
v___x_3499_ = lean_apply_2(v_toPure_3491_, lean_box(0), v___x_3498_);
return v___x_3499_;
}
}
v___jp_3502_:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Lean_Syntax_getTailPos_x3f(v_ref_3501_, v___x_3481_);
lean_dec(v_ref_3501_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_inc(v___y_3503_);
v___y_3489_ = v___y_3503_;
v___y_3490_ = v___y_3503_;
goto v___jp_3488_;
}
else
{
lean_object* v_val_3505_; 
v_val_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_val_3505_);
lean_dec_ref(v___x_3504_);
v___y_3489_ = v___y_3503_;
v___y_3490_ = v_val_3505_;
goto v___jp_3488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object* v_traceElem_3510_, lean_object* v_toApplicative_3511_, lean_object* v___f_3512_, lean_object* v___f_3513_, lean_object* v_____s_3514_, lean_object* v___x_3515_, lean_object* v_____do__lift_3516_){
_start:
{
uint8_t v___x_1943__boxed_3517_; lean_object* v_res_3518_; 
v___x_1943__boxed_3517_ = lean_unbox(v___x_3515_);
v_res_3518_ = l_Lean_addTraceAsMessages___redArg___lam__9(v_traceElem_3510_, v_toApplicative_3511_, v___f_3512_, v___f_3513_, v_____s_3514_, v___x_1943__boxed_3517_, v_____do__lift_3516_);
lean_dec(v_____do__lift_3516_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object* v_inst_3519_, lean_object* v_toApplicative_3520_, lean_object* v___f_3521_, lean_object* v___f_3522_, uint8_t v___x_3523_, lean_object* v_toBind_3524_, lean_object* v_traceElem_3525_, lean_object* v_____s_3526_){
_start:
{
lean_object* v_getRef_3527_; lean_object* v___x_3528_; lean_object* v___f_3529_; lean_object* v___x_3530_; 
v_getRef_3527_ = lean_ctor_get(v_inst_3519_, 0);
lean_inc(v_getRef_3527_);
lean_dec_ref(v_inst_3519_);
v___x_3528_ = lean_box(v___x_3523_);
v___f_3529_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_3529_, 0, v_traceElem_3525_);
lean_closure_set(v___f_3529_, 1, v_toApplicative_3520_);
lean_closure_set(v___f_3529_, 2, v___f_3521_);
lean_closure_set(v___f_3529_, 3, v___f_3522_);
lean_closure_set(v___f_3529_, 4, v_____s_3526_);
lean_closure_set(v___f_3529_, 5, v___x_3528_);
v___x_3530_ = lean_apply_4(v_toBind_3524_, lean_box(0), lean_box(0), v_getRef_3527_, v___f_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object* v_inst_3531_, lean_object* v_toApplicative_3532_, lean_object* v___f_3533_, lean_object* v___f_3534_, lean_object* v___x_3535_, lean_object* v_toBind_3536_, lean_object* v_traceElem_3537_, lean_object* v_____s_3538_){
_start:
{
uint8_t v___x_2003__boxed_3539_; lean_object* v_res_3540_; 
v___x_2003__boxed_3539_ = lean_unbox(v___x_3535_);
v_res_3540_ = l_Lean_addTraceAsMessages___redArg___lam__10(v_inst_3531_, v_toApplicative_3532_, v___f_3533_, v___f_3534_, v___x_2003__boxed_3539_, v_toBind_3536_, v_traceElem_3537_, v_____s_3538_);
return v_res_3540_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___f_3542_; 
v___x_3541_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_3542_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3542_, 0, v___x_3541_);
return v___f_3542_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___f_3543_; lean_object* v___f_3544_; 
v___f_3543_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__0, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0);
v___f_3544_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3544_, 0, v___f_3543_);
lean_closure_set(v___f_3544_, 1, v___f_3543_);
return v___f_3544_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4(void){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = lean_box(0);
v___x_3549_ = lean_unsigned_to_nat(16u);
v___x_3550_ = lean_mk_array(v___x_3549_, v___x_3548_);
return v___x_3550_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v_pos2traces_3553_; 
v___x_3551_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__4, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4);
v___x_3552_ = lean_unsigned_to_nat(0u);
v_pos2traces_3553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_3553_, 0, v___x_3552_);
lean_ctor_set(v_pos2traces_3553_, 1, v___x_3551_);
return v_pos2traces_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11(lean_object* v_inst_3554_, lean_object* v_toApplicative_3555_, lean_object* v_toBind_3556_, lean_object* v_inst_3557_, lean_object* v___f_3558_, lean_object* v_traces_3559_){
_start:
{
uint8_t v___x_3560_; 
v___x_3560_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___f_3561_; lean_object* v___f_3562_; lean_object* v___x_3563_; lean_object* v___f_3564_; lean_object* v_pos2traces_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___f_3561_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__1, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1);
v___f_3562_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___lam__11___closed__3));
v___x_3563_ = lean_box(v___x_3560_);
lean_inc(v_toBind_3556_);
v___f_3564_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3564_, 0, v_inst_3554_);
lean_closure_set(v___f_3564_, 1, v_toApplicative_3555_);
lean_closure_set(v___f_3564_, 2, v___f_3561_);
lean_closure_set(v___f_3564_, 3, v___f_3562_);
lean_closure_set(v___f_3564_, 4, v___x_3563_);
lean_closure_set(v___f_3564_, 5, v_toBind_3556_);
v_pos2traces_3565_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__5, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5);
v___x_3566_ = l_Lean_PersistentArray_forIn___redArg(v_inst_3557_, v_traces_3559_, v_pos2traces_3565_, v___f_3564_);
v___x_3567_ = lean_apply_4(v_toBind_3556_, lean_box(0), lean_box(0), v___x_3566_, v___f_3558_);
return v___x_3567_;
}
else
{
lean_object* v_toPure_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec(v___f_3558_);
lean_dec_ref(v_inst_3557_);
lean_dec(v_toBind_3556_);
lean_dec_ref(v_inst_3554_);
v_toPure_3568_ = lean_ctor_get(v_toApplicative_3555_, 1);
lean_inc(v_toPure_3568_);
lean_dec_ref(v_toApplicative_3555_);
v___x_3569_ = lean_box(0);
v___x_3570_ = lean_apply_2(v_toPure_3568_, lean_box(0), v___x_3569_);
return v___x_3570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___boxed(lean_object* v_inst_3571_, lean_object* v_toApplicative_3572_, lean_object* v_toBind_3573_, lean_object* v_inst_3574_, lean_object* v___f_3575_, lean_object* v_traces_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_addTraceAsMessages___redArg___lam__11(v_inst_3571_, v_toApplicative_3572_, v_toBind_3573_, v_inst_3574_, v___f_3575_, v_traces_3576_);
lean_dec_ref(v_traces_3576_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12(lean_object* v_toApplicative_3578_, lean_object* v_inst_3579_, lean_object* v_toBind_3580_, lean_object* v_inst_3581_, lean_object* v___f_3582_, lean_object* v___f_3583_, lean_object* v___f_3584_, lean_object* v_inst_3585_, lean_object* v_inst_3586_, lean_object* v_____do__lift_3587_){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3592_ = l_Lean_KVMap_instValueBool;
v___x_3593_ = l_Lean_KVMap_instValueString;
v___x_3594_ = l_Lean_trace_profiler_output;
v___x_3595_ = l_Lean_Option_get_x3f___redArg(v___x_3593_, v_____do__lift_3587_, v___x_3594_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3596_ = l_Lean_trace_profiler_serve;
v___x_3597_ = l_Lean_Option_get___redArg(v___x_3592_, v_____do__lift_3587_, v___x_3596_);
v___x_3598_ = lean_unbox(v___x_3597_);
lean_dec(v___x_3597_);
if (v___x_3598_ == 0)
{
uint8_t v___x_3599_; lean_object* v___x_3600_; lean_object* v___f_3601_; lean_object* v___f_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3599_ = 1;
v___x_3600_ = lean_box(v___x_3599_);
lean_inc_ref_n(v_inst_3581_, 2);
lean_inc_n(v_toBind_3580_, 2);
lean_inc_ref(v_toApplicative_3578_);
v___f_3601_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__8___boxed), 9, 8);
lean_closure_set(v___f_3601_, 0, v_toApplicative_3578_);
lean_closure_set(v___f_3601_, 1, v___x_3600_);
lean_closure_set(v___f_3601_, 2, v_inst_3579_);
lean_closure_set(v___f_3601_, 3, v_toBind_3580_);
lean_closure_set(v___f_3601_, 4, v_inst_3581_);
lean_closure_set(v___f_3601_, 5, v___f_3582_);
lean_closure_set(v___f_3601_, 6, v___f_3583_);
lean_closure_set(v___f_3601_, 7, v___f_3584_);
v___f_3602_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__11___boxed), 6, 5);
lean_closure_set(v___f_3602_, 0, v_inst_3585_);
lean_closure_set(v___f_3602_, 1, v_toApplicative_3578_);
lean_closure_set(v___f_3602_, 2, v_toBind_3580_);
lean_closure_set(v___f_3602_, 3, v_inst_3581_);
lean_closure_set(v___f_3602_, 4, v___f_3601_);
v___x_3603_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3581_, v_inst_3586_);
v___x_3604_ = lean_apply_4(v_toBind_3580_, lean_box(0), lean_box(0), v___x_3603_, v___f_3602_);
return v___x_3604_;
}
else
{
lean_dec_ref(v_inst_3586_);
lean_dec_ref(v_inst_3585_);
lean_dec_ref(v___f_3584_);
lean_dec_ref(v___f_3583_);
lean_dec(v___f_3582_);
lean_dec_ref(v_inst_3581_);
lean_dec(v_toBind_3580_);
lean_dec_ref(v_inst_3579_);
goto v___jp_3588_;
}
}
else
{
lean_dec_ref(v___x_3595_);
lean_dec_ref(v_inst_3586_);
lean_dec_ref(v_inst_3585_);
lean_dec_ref(v___f_3584_);
lean_dec_ref(v___f_3583_);
lean_dec(v___f_3582_);
lean_dec_ref(v_inst_3581_);
lean_dec(v_toBind_3580_);
lean_dec_ref(v_inst_3579_);
goto v___jp_3588_;
}
v___jp_3588_:
{
lean_object* v_toPure_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v_toPure_3589_ = lean_ctor_get(v_toApplicative_3578_, 1);
lean_inc(v_toPure_3589_);
lean_dec_ref(v_toApplicative_3578_);
v___x_3590_ = lean_box(0);
v___x_3591_ = lean_apply_2(v_toPure_3589_, lean_box(0), v___x_3590_);
return v___x_3591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12___boxed(lean_object* v_toApplicative_3605_, lean_object* v_inst_3606_, lean_object* v_toBind_3607_, lean_object* v_inst_3608_, lean_object* v___f_3609_, lean_object* v___f_3610_, lean_object* v___f_3611_, lean_object* v_inst_3612_, lean_object* v_inst_3613_, lean_object* v_____do__lift_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_addTraceAsMessages___redArg___lam__12(v_toApplicative_3605_, v_inst_3606_, v_toBind_3607_, v_inst_3608_, v___f_3609_, v___f_3610_, v___f_3611_, v_inst_3612_, v_inst_3613_, v_____do__lift_3614_);
lean_dec_ref(v_____do__lift_3614_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object* v_inst_3618_, lean_object* v_inst_3619_, lean_object* v_inst_3620_, lean_object* v_inst_3621_, lean_object* v_inst_3622_){
_start:
{
lean_object* v_toApplicative_3623_; lean_object* v_toBind_3624_; lean_object* v___f_3625_; lean_object* v___f_3626_; lean_object* v___f_3627_; lean_object* v___f_3628_; lean_object* v___x_3629_; 
v_toApplicative_3623_ = lean_ctor_get(v_inst_3619_, 0);
lean_inc_ref_n(v_toApplicative_3623_, 2);
v_toBind_3624_ = lean_ctor_get(v_inst_3619_, 1);
lean_inc_n(v_toBind_3624_, 2);
v___f_3625_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3625_, 0, v_toApplicative_3623_);
v___f_3626_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__0));
v___f_3627_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__1));
v___f_3628_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__12___boxed), 10, 9);
lean_closure_set(v___f_3628_, 0, v_toApplicative_3623_);
lean_closure_set(v___f_3628_, 1, v_inst_3621_);
lean_closure_set(v___f_3628_, 2, v_toBind_3624_);
lean_closure_set(v___f_3628_, 3, v_inst_3619_);
lean_closure_set(v___f_3628_, 4, v___f_3625_);
lean_closure_set(v___f_3628_, 5, v___f_3626_);
lean_closure_set(v___f_3628_, 6, v___f_3627_);
lean_closure_set(v___f_3628_, 7, v_inst_3620_);
lean_closure_set(v___f_3628_, 8, v_inst_3622_);
v___x_3629_ = lean_apply_4(v_toBind_3624_, lean_box(0), lean_box(0), v_inst_3618_, v___f_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object* v_m_3630_, lean_object* v_inst_3631_, lean_object* v_inst_3632_, lean_object* v_inst_3633_, lean_object* v_inst_3634_, lean_object* v_inst_3635_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_addTraceAsMessages___redArg(v_inst_3631_, v_inst_3632_, v_inst_3633_, v_inst_3634_, v_inst_3635_);
return v___x_3636_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3678_ = lean_unsigned_to_nat(2826257906u);
v___x_3679_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3680_ = l_Lean_Name_num___override(v___x_3679_, v___x_3678_);
return v___x_3680_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3682_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3683_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3684_ = l_Lean_Name_str___override(v___x_3683_, v___x_3682_);
return v___x_3684_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3687_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3688_ = l_Lean_Name_str___override(v___x_3687_, v___x_3686_);
return v___x_3688_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3689_ = lean_unsigned_to_nat(2u);
v___x_3690_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3691_ = l_Lean_Name_num___override(v___x_3690_, v___x_3689_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3693_; uint8_t v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3693_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3694_ = 0;
v___x_3695_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3696_ = l_Lean_registerTraceClass(v___x_3693_, v___x_3694_, v___x_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object* v_a_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
return v_res_3698_;
}
}
lean_object* runtime_initialize_Lean_Elab_Exception(uint8_t builtin);
lean_object* runtime_initialize_Lean_Log(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Trace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedTraceElem_default = _init_l_Lean_instInhabitedTraceElem_default();
lean_mark_persistent(l_Lean_instInhabitedTraceElem_default);
l_Lean_instInhabitedTraceElem = _init_l_Lean_instInhabitedTraceElem();
lean_mark_persistent(l_Lean_instInhabitedTraceElem);
l_Lean_instInhabitedTraceState_default = _init_l_Lean_instInhabitedTraceState_default();
lean_mark_persistent(l_Lean_instInhabitedTraceState_default);
l_Lean_instInhabitedTraceState = _init_l_Lean_instInhabitedTraceState();
lean_mark_persistent(l_Lean_instInhabitedTraceState);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_inheritedTraceOptions = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_inheritedTraceOptions);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_threshold);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_useHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_useHeartbeats);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_output = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_output);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_serve = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_serve);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_output_pp = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_output_pp);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_Trace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_MonadTrace_getInheritedTraceOptions___autoParam = _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam();
lean_mark_persistent(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam);
l_Lean_registerTraceClass___auto__1 = _init_l_Lean_registerTraceClass___auto__1();
lean_mark_persistent(l_Lean_registerTraceClass___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Exception(uint8_t builtin);
lean_object* initialize_Lean_Log(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Trace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Trace(builtin);
}
#ifdef __cplusplus
}
#endif
