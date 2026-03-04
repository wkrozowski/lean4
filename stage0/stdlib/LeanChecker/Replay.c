// Lean compiler output
// Module: LeanChecker.Replay
// Imports: public import Lean.CoreM public import Lean.AddDecl public import Lean.Util.FoldConsts
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo_default;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_throwAlreadyImported_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "while replaying declaration '"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__0 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__0_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "':\n"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__1 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__1_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__2 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__2_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Environment_Replay_x27_replayConstant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__3 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__3_value;
lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstants(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__6 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__6_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Environment.Replay'.replayConstant"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__5 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__5_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LeanChecker.Replay"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__4 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__4_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Environment_Replay_x27_replayConstant___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__7;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstants___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "No such constructor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Invalid constructor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqConstructorVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "No such recursor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Invalid recursor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqRecursorVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_elab_environment_of_kernel_env(lean_object*);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_26; 
x_9 = lean_st_ref_take(x_2);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 2);
x_13 = lean_ctor_get(x_9, 3);
x_14 = lean_ctor_get(x_9, 4);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_15 = x_9;
x_16 = x_26;
goto block_25;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_1, x_11);
x_18 = l_Lean_NameSet_insert(x_12, x_1);
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_18);
lean_ctor_set(x_15, 1, x_17);
x_19 = x_15;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set(x_24, 4, x_14);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_st_ref_set(x_2, x_19);
x_21 = lean_box(x_6);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_x27_isTodo___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_isTodo___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_isTodo(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Options_empty;
x_4 = l_Lean_Kernel_Exception_toMessageData(x_1, x_3);
x_5 = l_Lean_MessageData_toString(x_4);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_Replay_x27_throwKernelException___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_throwKernelException___redArg(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_throwKernelException(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = 0;
x_7 = lean_box(0);
x_8 = lean_add_decl(x_5, x_6, x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_Environment_Replay_x27_throwKernelException___redArg(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_33; 
x_11 = lean_ctor_get(x_8, 0);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
x_12 = x_8;
x_13 = x_33;
goto block_32;
}
else
{
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_30; 
x_14 = lean_st_ref_take(x_2);
x_15 = lean_ctor_get(x_14, 1);
x_16 = lean_ctor_get(x_14, 2);
x_17 = lean_ctor_get(x_14, 3);
x_18 = lean_ctor_get(x_14, 4);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_14, 0);
lean_dec(x_31);
x_19 = x_14;
x_20 = x_30;
goto block_29;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_21; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_11);
x_21 = x_19;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_16);
lean_ctor_set(x_28, 3, x_17);
lean_ctor_set(x_28, 4, x_18);
x_21 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_st_ref_set(x_2, x_21);
x_23 = lean_box(0);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_23);
x_24 = x_12;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_addDecl(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_obj_once(&l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0, &l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0_once, _init_l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0);
x_6 = l_ReaderT_instMonad___redArg(x_5);
x_7 = lean_box(0);
x_8 = l_instInhabitedOfMonad___redArg(x_6, x_7);
x_9 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_3(x_10, x_2, x_3, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_22; 
x_6 = lean_st_ref_take(x_4);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 2);
x_10 = lean_ctor_get(x_6, 3);
x_11 = lean_ctor_get(x_6, 4);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
x_12 = x_6;
x_13 = x_22;
goto block_21;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_1, x_9);
if (x_13 == 0)
{
lean_ctor_set(x_12, 2, x_14);
x_15 = x_12;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_10);
lean_ctor_set(x_20, 4, x_11);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_st_ref_set(x_4, x_15);
x_17 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0));
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_7, x_5);
lean_dec_ref(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_4(x_2, x_9, x_4, x_5, lean_box(0));
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_8, 0);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
x_12 = x_8;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Environment_Replay_x27_replayConstant___lam__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_apply_4(x_1, x_6, x_3, x_4, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Environment_Replay_x27_replayConstant___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_16; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
x_6 = x_1;
x_7 = x_16;
goto block_15;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_ConstantInfo_name(x_4);
x_9 = l_Lean_ConstantInfo_type(x_4);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_10);
x_11 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_2);
x_11 = x_14;
goto block_13;
}
block_13:
{
x_1 = x_5;
x_2 = x_11;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
x_6 = x_1;
x_7 = x_20;
goto block_19;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_ConstantInfo_name(x_8);
x_11 = l_Lean_ConstantInfo_type(x_8);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__0(x_9, x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_14);
x_15 = x_6;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_2);
x_15 = x_18;
goto block_17;
}
block_17:
{
x_1 = x_5;
x_2 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_26; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_st_ref_take(x_3);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 2);
x_12 = lean_ctor_get(x_8, 3);
x_13 = lean_ctor_get(x_8, 4);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
x_14 = x_8;
x_15 = x_26;
goto block_25;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_ConstantInfo_name(x_6);
x_17 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_16, x_10);
x_18 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_16, x_11);
lean_dec(x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 2, x_18);
lean_ctor_set(x_14, 1, x_17);
x_19 = x_14;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_12);
lean_ctor_set(x_24, 4, x_13);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_st_ref_set(x_3, x_19);
x_21 = lean_box(0);
x_1 = x_7;
x_2 = x_21;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_reverse___redArg(x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_18; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_9 = x_1;
x_10 = x_18;
goto block_17;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_instInhabitedConstantInfo_default;
x_12 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_throwAlreadyImported_spec__0___redArg(x_11, x_3, x_7);
lean_dec(x_7);
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_12);
x_13 = x_9;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_2);
x_13 = x_16;
goto block_15;
}
block_15:
{
x_1 = x_8;
x_2 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_List_reverse___redArg(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_23; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
x_10 = x_1;
x_11 = x_23;
goto block_22;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_ConstantInfo_inductiveVal_x21(x_8);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_box(0);
x_15 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(x_13, x_14, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 0, x_17);
x_18 = x_10;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_2);
x_18 = x_21;
goto block_20;
}
block_20:
{
x_1 = x_9;
x_2 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
x_10 = l_Lean_Environment_Replay_x27_replayConstants(x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = lean_box(0);
x_1 = x_8;
x_2 = x_11;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
lean_inc(x_4);
lean_inc_ref(x_3);
x_11 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(x_9, x_10, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_dec_ref(x_11);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Environment_Replay_x27_replayConstant___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__6));
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_unsigned_to_nat(81u);
x_4 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__5));
x_5 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_Environment_Replay_x27_isTodo___redArg(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_207; 
x_6 = lean_ctor_get(x_5, 0);
x_207 = !lean_is_exclusive(x_5);
if (x_207 == 0)
{
x_7 = x_5;
x_8 = x_207;
goto block_206;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_207;
goto block_206;
}
block_206:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
x_14 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(x_2, x_1);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_203; 
x_15 = lean_ctor_get(x_14, 0);
x_203 = !lean_is_exclusive(x_14);
if (x_203 == 0)
{
x_16 = x_14;
x_17 = x_203;
goto block_202;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_203;
goto block_202;
}
block_202:
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_15);
x_18 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_15);
lean_inc(x_3);
lean_inc_ref(x_2);
x_19 = l_Lean_Environment_Replay_x27_replayConstants(x_18, x_2, x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; uint8_t x_200; 
x_200 = !lean_is_exclusive(x_19);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_19, 0);
lean_dec(x_201);
x_20 = x_19;
x_21 = x_200;
goto block_199;
}
else
{
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = x_200;
goto block_199;
}
block_199:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_41; 
x_22 = lean_st_ref_get(x_3);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_1, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_del_object(x_20);
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_53 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_53);
x_54 = x_7;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_53);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
else
{
lean_object* x_57; 
lean_inc(x_1);
x_57 = lean_alloc_closure((void*)(l_Lean_Environment_Replay_x27_replayConstant___lam__0___boxed), 5, 1);
lean_closure_set(x_57, 0, x_1);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_69; 
lean_dec_ref(x_57);
lean_del_object(x_7);
x_58 = lean_ctor_get(x_15, 0);
x_69 = !lean_is_exclusive(x_15);
if (x_69 == 0)
{
x_59 = x_15;
x_60 = x_69;
goto block_68;
}
else
{
lean_inc(x_58);
lean_dec(x_15);
x_59 = lean_box(0);
x_60 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_58);
x_61 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_62; 
x_62 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_61, x_3);
lean_dec_ref(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_63, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = x_64;
goto block_52;
}
else
{
lean_object* x_65; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec_ref(x_62);
x_25 = x_65;
x_26 = lean_box(0);
goto block_40;
}
}
}
}
case 1:
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_81; 
lean_dec_ref(x_57);
lean_del_object(x_7);
x_70 = lean_ctor_get(x_15, 0);
x_81 = !lean_is_exclusive(x_15);
if (x_81 == 0)
{
x_71 = x_15;
x_72 = x_81;
goto block_80;
}
else
{
lean_inc(x_70);
lean_dec(x_15);
x_71 = lean_box(0);
x_72 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_73; 
if (x_72 == 0)
{
x_73 = x_71;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_70);
x_73 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_74; 
x_74 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_73, x_3);
lean_dec_ref(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_75, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = x_76;
goto block_52;
}
else
{
lean_object* x_77; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
lean_dec_ref(x_74);
x_25 = x_77;
x_26 = lean_box(0);
goto block_40;
}
}
}
}
case 2:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_82);
x_83 = lean_st_ref_get(x_3);
x_84 = lean_ctor_get(x_83, 0);
lean_inc_ref(x_84);
lean_dec(x_83);
lean_inc_ref(x_57);
lean_inc_ref(x_82);
x_85 = lean_alloc_closure((void*)(l_Lean_Environment_Replay_x27_replayConstant___lam__1___boxed), 6, 2);
lean_closure_set(x_85, 0, x_82);
lean_closure_set(x_85, 1, x_57);
x_89 = l_Lean_ConstantInfo_name(x_15);
lean_dec_ref(x_15);
x_90 = lean_environment_find(x_84, x_89);
if (lean_obj_tag(x_90) == 1)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 2)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_111; 
lean_dec_ref(x_90);
lean_dec_ref(x_85);
x_92 = lean_ctor_get(x_82, 0);
x_93 = lean_ctor_get(x_91, 0);
lean_inc_ref(x_93);
lean_dec_ref(x_91);
x_94 = lean_ctor_get(x_93, 0);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_82, 2);
x_96 = lean_ctor_get(x_92, 0);
x_97 = lean_ctor_get(x_92, 1);
x_98 = lean_ctor_get(x_92, 2);
x_99 = lean_ctor_get(x_93, 2);
lean_inc(x_99);
lean_dec_ref(x_93);
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_94, 2);
lean_inc_ref(x_102);
lean_dec_ref(x_94);
x_111 = lean_name_eq(x_96, x_100);
lean_dec(x_100);
if (x_111 == 0)
{
lean_dec_ref(x_102);
x_103 = x_111;
goto block_110;
}
else
{
uint8_t x_112; 
x_112 = lean_expr_eqv(x_98, x_102);
lean_dec_ref(x_102);
x_103 = x_112;
goto block_110;
}
block_110:
{
if (x_103 == 0)
{
lean_dec(x_101);
lean_dec(x_99);
lean_del_object(x_7);
goto block_88;
}
else
{
uint8_t x_104; 
x_104 = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(x_97, x_101);
lean_dec(x_101);
if (x_104 == 0)
{
lean_dec(x_99);
lean_del_object(x_7);
goto block_88;
}
else
{
uint8_t x_105; 
x_105 = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(x_95, x_99);
lean_dec(x_99);
if (x_105 == 0)
{
lean_del_object(x_7);
goto block_88;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_82);
lean_dec_ref(x_57);
lean_del_object(x_20);
lean_del_object(x_16);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_106 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_106);
x_107 = x_7;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_106);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_91);
lean_dec_ref(x_82);
lean_dec_ref(x_57);
lean_del_object(x_7);
x_113 = l_Lean_Environment_Replay_x27_replayConstant___lam__2(x_85, x_90, x_2, x_3);
lean_dec_ref(x_90);
x_41 = x_113;
goto block_52;
}
}
else
{
lean_object* x_114; 
lean_dec_ref(x_82);
lean_dec_ref(x_57);
lean_del_object(x_7);
x_114 = l_Lean_Environment_Replay_x27_replayConstant___lam__2(x_85, x_90, x_2, x_3);
lean_dec(x_90);
x_41 = x_114;
goto block_52;
}
block_88:
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_box(0);
x_87 = l_Lean_Environment_Replay_x27_replayConstant___lam__1(x_82, x_57, x_86, x_2, x_3);
x_41 = x_87;
goto block_52;
}
}
case 3:
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_126; 
lean_dec_ref(x_57);
lean_del_object(x_7);
x_115 = lean_ctor_get(x_15, 0);
x_126 = !lean_is_exclusive(x_15);
if (x_126 == 0)
{
x_116 = x_15;
x_117 = x_126;
goto block_125;
}
else
{
lean_inc(x_115);
lean_dec(x_15);
x_116 = lean_box(0);
x_117 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_118; 
if (x_117 == 0)
{
x_118 = x_116;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_124, 0, x_115);
x_118 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_119; 
x_119 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_118, x_3);
lean_dec_ref(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_120, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = x_121;
goto block_52;
}
else
{
lean_object* x_122; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
lean_dec_ref(x_119);
x_25 = x_122;
x_26 = lean_box(0);
goto block_40;
}
}
}
}
case 4:
{
lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_15);
lean_dec_ref(x_57);
lean_del_object(x_7);
x_127 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__3));
lean_inc(x_3);
lean_inc_ref(x_2);
x_128 = l_Lean_Environment_Replay_x27_replayConstant(x_127, x_2, x_3);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec_ref(x_128);
x_129 = lean_box(4);
x_130 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_129, x_3);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_131, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = x_132;
goto block_52;
}
else
{
lean_object* x_133; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
lean_dec_ref(x_130);
x_25 = x_133;
x_26 = lean_box(0);
goto block_40;
}
}
else
{
lean_object* x_134; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_134 = lean_ctor_get(x_128, 0);
lean_inc(x_134);
lean_dec_ref(x_128);
x_25 = x_134;
x_26 = lean_box(0);
goto block_40;
}
}
case 5:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec_ref(x_57);
lean_del_object(x_7);
x_135 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_135);
lean_dec_ref(x_15);
x_136 = lean_ctor_get(x_135, 0);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 3);
lean_inc(x_138);
lean_dec_ref(x_135);
x_139 = lean_box(0);
x_140 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(x_138, x_139, x_2);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_box(0);
x_143 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(x_141, x_142, x_3);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
lean_dec_ref(x_143);
x_144 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(x_141, x_139, x_2, x_3);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_145);
x_146 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(x_145, x_142, x_2, x_3);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_146);
x_147 = lean_ctor_get(x_136, 1);
lean_inc(x_147);
lean_dec_ref(x_136);
x_148 = l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__6(x_145, x_139);
x_149 = 0;
x_150 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_137);
lean_ctor_set(x_150, 2, x_148);
lean_ctor_set_uint8(x_150, sizeof(void*)*3, x_149);
x_151 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_150, x_3);
lean_dec_ref(x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
x_153 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_152, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = x_153;
goto block_52;
}
else
{
lean_object* x_154; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
lean_dec_ref(x_151);
x_25 = x_154;
x_26 = lean_box(0);
goto block_40;
}
}
else
{
lean_object* x_155; 
lean_dec(x_145);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_3);
lean_dec_ref(x_2);
x_155 = lean_ctor_get(x_146, 0);
lean_inc(x_155);
lean_dec_ref(x_146);
x_25 = x_155;
x_26 = lean_box(0);
goto block_40;
}
}
else
{
lean_object* x_156; 
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_3);
lean_dec_ref(x_2);
x_156 = lean_ctor_get(x_144, 0);
lean_inc(x_156);
lean_dec_ref(x_144);
x_25 = x_156;
x_26 = lean_box(0);
goto block_40;
}
}
else
{
lean_object* x_157; 
lean_dec(x_141);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_3);
lean_dec_ref(x_2);
x_157 = lean_ctor_get(x_143, 0);
lean_inc(x_157);
lean_dec_ref(x_143);
x_25 = x_157;
x_26 = lean_box(0);
goto block_40;
}
}
else
{
lean_object* x_158; 
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_3);
lean_dec_ref(x_2);
x_158 = lean_ctor_get(x_140, 0);
lean_inc(x_158);
lean_dec_ref(x_140);
x_25 = x_158;
x_26 = lean_box(0);
goto block_40;
}
}
case 6:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_178; 
lean_dec_ref(x_57);
lean_del_object(x_7);
x_159 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_159);
lean_dec_ref(x_15);
x_160 = lean_st_ref_take(x_3);
x_161 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_161);
lean_dec_ref(x_159);
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_ctor_get(x_160, 1);
x_164 = lean_ctor_get(x_160, 2);
x_165 = lean_ctor_get(x_160, 3);
x_166 = lean_ctor_get(x_160, 4);
x_178 = !lean_is_exclusive(x_160);
if (x_178 == 0)
{
x_167 = x_160;
x_168 = x_178;
goto block_177;
}
else
{
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_160);
x_167 = lean_box(0);
x_168 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_161, 0);
lean_inc(x_169);
lean_dec_ref(x_161);
x_170 = l_Lean_NameSet_insert(x_165, x_169);
if (x_168 == 0)
{
lean_ctor_set(x_167, 3, x_170);
x_171 = x_167;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_176, 0, x_162);
lean_ctor_set(x_176, 1, x_163);
lean_ctor_set(x_176, 2, x_164);
lean_ctor_set(x_176, 3, x_170);
lean_ctor_set(x_176, 4, x_166);
x_171 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_st_ref_set(x_3, x_171);
x_173 = lean_box(0);
x_174 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_173, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = x_174;
goto block_52;
}
}
}
default: 
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_198; 
lean_dec_ref(x_57);
lean_del_object(x_7);
x_179 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_179);
lean_dec_ref(x_15);
x_180 = lean_st_ref_take(x_3);
x_181 = lean_ctor_get(x_179, 0);
lean_inc_ref(x_181);
lean_dec_ref(x_179);
x_182 = lean_ctor_get(x_180, 0);
x_183 = lean_ctor_get(x_180, 1);
x_184 = lean_ctor_get(x_180, 2);
x_185 = lean_ctor_get(x_180, 3);
x_186 = lean_ctor_get(x_180, 4);
x_198 = !lean_is_exclusive(x_180);
if (x_198 == 0)
{
x_187 = x_180;
x_188 = x_198;
goto block_197;
}
else
{
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_180);
x_187 = lean_box(0);
x_188 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_181, 0);
lean_inc(x_189);
lean_dec_ref(x_181);
x_190 = l_Lean_NameSet_insert(x_186, x_189);
if (x_188 == 0)
{
lean_ctor_set(x_187, 4, x_190);
x_191 = x_187;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_196, 0, x_182);
lean_ctor_set(x_196, 1, x_183);
lean_ctor_set(x_196, 2, x_184);
lean_ctor_set(x_196, 3, x_185);
lean_ctor_set(x_196, 4, x_190);
x_191 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_st_ref_set(x_3, x_191);
x_193 = lean_box(0);
x_194 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_193, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = x_194;
goto block_52;
}
}
}
}
}
block_40:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__0));
x_28 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_24);
x_29 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
x_30 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__1));
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_io_error_to_string(x_25);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 18);
lean_ctor_set(x_16, 0, x_33);
x_34 = x_16;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_33);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_34);
x_35 = x_20;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
block_52:
{
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_50; 
lean_del_object(x_20);
lean_del_object(x_16);
lean_dec(x_1);
x_42 = lean_ctor_get(x_41, 0);
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
x_43 = x_41;
x_44 = x_50;
goto block_49;
}
else
{
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
if (x_44 == 0)
{
lean_ctor_set(x_43, 0, x_45);
x_46 = x_43;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
lean_dec_ref(x_41);
x_25 = x_51;
x_26 = lean_box(0);
goto block_40;
}
}
}
}
else
{
lean_del_object(x_16);
lean_dec(x_15);
lean_del_object(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_19;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_14);
lean_del_object(x_7);
lean_dec(x_1);
x_204 = lean_obj_once(&l_Lean_Environment_Replay_x27_replayConstant___closed__7, &l_Lean_Environment_Replay_x27_replayConstant___closed__7_once, _init_l_Lean_Environment_Replay_x27_replayConstant___closed__7);
x_205 = l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(x_204, x_2, x_3);
return x_205;
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_215; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_208 = lean_ctor_get(x_5, 0);
x_215 = !lean_is_exclusive(x_5);
if (x_215 == 0)
{
x_209 = x_5;
x_210 = x_215;
goto block_214;
}
else
{
lean_inc(x_208);
lean_dec(x_5);
x_209 = lean_box(0);
x_210 = x_215;
goto block_214;
}
block_214:
{
lean_object* x_211; 
if (x_210 == 0)
{
x_211 = x_209;
goto block_212;
}
else
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_208);
x_211 = x_213;
goto block_212;
}
block_212:
{
return x_211;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc(x_4);
lean_inc_ref(x_3);
x_9 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(x_1, x_7, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_9);
lean_inc(x_4);
lean_inc_ref(x_3);
x_10 = l_Lean_Environment_Replay_x27_replayConstant(x_6, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = lean_box(0);
x_1 = x_11;
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_10, 0);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
x_14 = x_10;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstants(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(x_5, x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_7 = x_6;
x_8 = x_13;
goto block_12;
}
else
{
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_9; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_5);
x_9 = x_7;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_6, 0);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
x_16 = x_6;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstants___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_replayConstants(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_replayConstant(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(x_2, x_3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_17; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec_ref(x_2);
x_17 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(x_1, x_7, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_46; 
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_17, 0);
lean_dec(x_47);
x_18 = x_17;
x_19 = x_46;
goto block_45;
}
else
{
lean_dec(x_17);
x_18 = lean_box(0);
x_19 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_st_ref_get(x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec(x_20);
lean_inc(x_6);
x_22 = lean_environment_find(x_21, x_6);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_23) == 6)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(x_3, x_6);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_obj_tag(x_26) == 6)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_44; 
x_27 = lean_ctor_get(x_26, 0);
x_44 = !lean_is_exclusive(x_26);
if (x_44 == 0)
{
x_28 = x_26;
x_29 = x_44;
goto block_43;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_44;
goto block_43;
}
block_43:
{
uint8_t x_30; 
x_30 = l_Lean_instBEqConstructorVal_beq(x_24, x_27);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
x_31 = 1;
x_32 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1));
x_33 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_31);
x_34 = lean_string_append(x_32, x_33);
lean_dec_ref(x_33);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 18);
lean_ctor_set(x_28, 0, x_34);
x_35 = x_28;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_34);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_35);
x_36 = x_18;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
else
{
lean_object* x_41; 
lean_del_object(x_28);
lean_del_object(x_18);
lean_dec(x_6);
x_41 = lean_box(0);
x_1 = x_41;
x_2 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_26);
lean_dec_ref(x_24);
lean_del_object(x_18);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_del_object(x_18);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_23);
lean_del_object(x_18);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_22);
lean_del_object(x_18);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
return x_17;
}
block_16:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__0));
x_11 = 1;
x_12 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_1);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(x_6, x_5, x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_8 = x_7;
x_9 = x_14;
goto block_13;
}
else
{
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_10; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_6);
x_10 = x_8;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_7, 0);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
x_17 = x_7;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_x27_checkPostponedConstructors(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_17; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec_ref(x_2);
x_17 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(x_1, x_7, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_46; 
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_17, 0);
lean_dec(x_47);
x_18 = x_17;
x_19 = x_46;
goto block_45;
}
else
{
lean_dec(x_17);
x_18 = lean_box(0);
x_19 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_st_ref_get(x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec(x_20);
lean_inc(x_6);
x_22 = lean_environment_find(x_21, x_6);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_23) == 7)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(x_3, x_6);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_obj_tag(x_26) == 7)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_44; 
x_27 = lean_ctor_get(x_26, 0);
x_44 = !lean_is_exclusive(x_26);
if (x_44 == 0)
{
x_28 = x_26;
x_29 = x_44;
goto block_43;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_44;
goto block_43;
}
block_43:
{
uint8_t x_30; 
x_30 = l_Lean_instBEqRecursorVal_beq(x_24, x_27);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
x_31 = 1;
x_32 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1));
x_33 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_31);
x_34 = lean_string_append(x_32, x_33);
lean_dec_ref(x_33);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 18);
lean_ctor_set(x_28, 0, x_34);
x_35 = x_28;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_34);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_35);
x_36 = x_18;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
else
{
lean_object* x_41; 
lean_del_object(x_28);
lean_del_object(x_18);
lean_dec(x_6);
x_41 = lean_box(0);
x_1 = x_41;
x_2 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_26);
lean_dec_ref(x_24);
lean_del_object(x_18);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_del_object(x_18);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_23);
lean_del_object(x_18);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_22);
lean_del_object(x_18);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
return x_17;
}
block_16:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0));
x_11 = 1;
x_12 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_1);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(x_6, x_5, x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_8 = x_7;
x_9 = x_14;
goto block_13;
}
else
{
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_10; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_6);
x_10 = x_8;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_7, 0);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
x_17 = x_7;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_x27_checkPostponedRecursors(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget_borrowed(x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(x_4, x_8);
lean_dec(x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_ConstantInfo_isUnsafe(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_ConstantInfo_isPartial(x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_NameSet_insert(x_2, x_7);
x_1 = x_6;
x_2 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_1 = x_6;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
x_1 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_box(1);
x_47 = lean_box(0);
x_48 = lean_array_get_size(x_26);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_lt(x_49, x_48);
if (x_50 == 0)
{
x_28 = x_47;
goto block_46;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = lean_usize_of_nat(x_48);
x_52 = 0;
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(x_26, x_51, x_52, x_47);
x_28 = x_53;
goto block_46;
}
block_25:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_6 = x_5;
x_7 = x_15;
goto block_14;
}
else
{
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = lean_elab_environment_of_kernel_env(x_9);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_10);
x_11 = x_6;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_5, 0);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
x_18 = x_5;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
block_46:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(x_28, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_elab_environment_to_kernel_env(x_2);
lean_inc(x_30);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_27);
lean_ctor_set(x_32, 4, x_27);
x_33 = lean_st_mk_ref(x_32);
x_34 = lean_box(0);
lean_inc(x_33);
lean_inc_ref(x_1);
x_35 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(x_34, x_30, x_1, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec_ref(x_35);
x_36 = l_Lean_Environment_Replay_x27_checkPostponedConstructors(x_1, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec_ref(x_36);
x_37 = l_Lean_Environment_Replay_x27_checkPostponedRecursors(x_1, x_33);
lean_dec_ref(x_1);
x_4 = x_33;
x_5 = x_37;
goto block_25;
}
else
{
lean_dec_ref(x_1);
x_4 = x_33;
x_5 = x_36;
goto block_25;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_33);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_35, 0);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
x_39 = x_35;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_replay_x27(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanChecker_Replay(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
