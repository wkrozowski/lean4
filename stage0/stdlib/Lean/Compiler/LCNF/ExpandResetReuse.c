// Lean compiler output
// Module: Lean.Compiler.LCNF.ExpandResetReuse
// Imports: public import Lean.Compiler.LCNF.PassManager import Init.While
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
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2_value;
lean_object* l_Array_instInhabited(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Compiler.LCNF.ExpandResetReuse"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.eraseProjIncFor"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__2_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "assertion violation: n > 0 -- 0 incs should not be happening\n      "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__3_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__7;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.remapSets"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.partitionSelfSets"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unused"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 23, 1, 196, 228, 87, 228, 117)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3_value;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reuseFailAlloc"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 58, 180, 100, 190, 122, 70, 27)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1_value;
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reusejp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 245, 4, 252, 178, 144, 44, 230)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "assertion violation: n == 1 -- n must be one since `resetToken := reset ...`\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.processResetCont"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isShared"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 21, 27, 150, 131, 176, 68, 226)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "resetjp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 44, 28, 106, 212, 154, 129, 104)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "isSharedCheck"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 46, 40, 117, 142, 84, 34, 112)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__6_value;
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expandResetReuse"};
static const lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_expandResetReuse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 183, 62, 154, 7, 128, 85, 195)}};
static const lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_expandResetReuse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__2_value;
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_expandResetReuse;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 164, 249, 156, 95, 195, 57, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ExpandResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 11, 111, 203, 109, 196, 117, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(154, 243, 191, 84, 138, 53, 176, 74)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 105, 247, 180, 77, 138, 39, 85)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 100, 40, 107, 220, 34, 211, 1)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 232, 133, 20, 223, 27, 247, 220)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 148, 15, 20, 202, 87, 70, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 233, 102, 190, 62, 169, 58, 201)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 94, 182, 88, 148, 161, 255, 83)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 201, 67, 31, 121, 57, 98)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 72, 63, 210, 236, 125, 229)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 64, 204, 59, 236, 250, 223, 228)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_45; 
x_7 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
x_8 = l_ReaderT_instMonad___redArg(x_7);
x_9 = lean_ctor_get(x_8, 0);
x_45 = !lean_is_exclusive(x_8);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_8, 1);
lean_dec(x_46);
x_10 = x_8;
x_11 = x_45;
goto block_44;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_42; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_9, 1);
lean_dec(x_43);
x_16 = x_9;
x_17 = x_42;
goto block_41;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
x_19 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_14);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_13);
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_23);
lean_ctor_set(x_16, 3, x_24);
lean_ctor_set(x_16, 2, x_25);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_22);
x_26 = x_16;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_18);
lean_ctor_set(x_40, 2, x_25);
lean_ctor_set(x_40, 3, x_24);
lean_ctor_set(x_40, 4, x_23);
x_26 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_27; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_26);
x_27 = x_10;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_19);
x_27 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_instInhabitedOfMonad___redArg(x_28, x_32);
x_34 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_panic_fn(x_34, x_1);
x_36 = lean_apply_5(x_35, x_2, x_3, x_4, x_5, lean_box(0));
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__3));
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(87u);
x_4 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__2));
x_5 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_138; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 0);
x_138 = !lean_is_exclusive(x_2);
if (x_138 == 0)
{
x_17 = x_2;
x_18 = x_138;
goto block_137;
}
else
{
lean_inc(x_15);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = x_138;
goto block_137;
}
block_14:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_2 = x_12;
goto _start;
}
block_137:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_136; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_136 = !lean_is_exclusive(x_15);
if (x_136 == 0)
{
x_21 = x_15;
x_22 = x_136;
goto block_135;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_23; lean_object* x_32; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_array_get_size(x_16);
x_39 = lean_nat_dec_le(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_del_object(x_21);
lean_del_object(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_20);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_16);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0);
x_44 = l_Array_back_x21___redArg(x_43, x_16);
switch (lean_obj_tag(x_44)) {
case 0:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
lean_dec_ref(x_45);
switch (lean_obj_tag(x_46)) {
case 8:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_46);
lean_del_object(x_21);
lean_del_object(x_17);
x_47 = lean_array_pop(x_16);
x_48 = lean_array_push(x_19, x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_20);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_2 = x_50;
goto _start;
}
case 7:
{
lean_object* x_52; uint8_t x_53; uint8_t x_62; 
lean_del_object(x_21);
lean_del_object(x_17);
x_62 = !lean_is_exclusive(x_46);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_46, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_46, 0);
lean_dec(x_64);
x_52 = x_46;
x_53 = x_62;
goto block_61;
}
else
{
lean_dec(x_46);
x_52 = lean_box(0);
x_53 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_array_pop(x_16);
x_55 = lean_array_push(x_19, x_44);
if (x_53 == 0)
{
lean_ctor_set_tag(x_52, 0);
lean_ctor_set(x_52, 1, x_20);
lean_ctor_set(x_52, 0, x_55);
x_56 = x_52;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_20);
x_56 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_2 = x_57;
goto _start;
}
}
}
default: 
{
lean_dec(x_46);
lean_dec_ref(x_44);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_23 = lean_box(0);
goto block_31;
}
}
}
case 7:
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; uint8_t x_134; 
lean_del_object(x_21);
lean_del_object(x_17);
x_65 = lean_ctor_get(x_44, 0);
x_66 = lean_ctor_get(x_44, 1);
x_67 = lean_ctor_get_uint8(x_44, sizeof(void*)*2);
x_68 = lean_ctor_get_uint8(x_44, sizeof(void*)*2 + 1);
x_134 = !lean_is_exclusive(x_44);
if (x_134 == 0)
{
x_69 = x_44;
x_70 = x_134;
goto block_133;
}
else
{
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_44);
x_69 = lean_box(0);
x_70 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_lt(x_71, x_66);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_del_object(x_69);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
x_73 = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__4);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_74 = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(x_73, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_85; 
x_75 = lean_ctor_get(x_74, 0);
x_85 = !lean_is_exclusive(x_74);
if (x_85 == 0)
{
x_76 = x_74;
x_77 = x_85;
goto block_84;
}
else
{
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_box(0);
x_77 = x_85;
goto block_84;
}
block_84:
{
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec_ref(x_75);
if (x_77 == 0)
{
lean_ctor_set(x_76, 0, x_78);
x_79 = x_76;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_78);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
else
{
lean_object* x_82; 
lean_del_object(x_76);
x_82 = lean_ctor_get(x_75, 0);
lean_inc(x_82);
lean_dec_ref(x_75);
x_2 = x_82;
goto _start;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_86 = lean_ctor_get(x_74, 0);
x_93 = !lean_is_exclusive(x_74);
if (x_93 == 0)
{
x_87 = x_74;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_74);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_nat_sub(x_38, x_37);
x_95 = lean_array_get(x_43, x_16, x_94);
lean_dec(x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
x_97 = lean_ctor_get(x_96, 3);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 6)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_132; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_132 = !lean_is_exclusive(x_97);
if (x_132 == 0)
{
x_101 = x_97;
x_102 = x_132;
goto block_131;
}
else
{
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_97);
x_101 = lean_box(0);
x_102 = x_132;
goto block_131;
}
block_131:
{
uint8_t x_103; uint8_t x_129; 
x_129 = l_Lean_instBEqFVarId_beq(x_98, x_65);
if (x_129 == 0)
{
lean_dec(x_100);
x_103 = x_129;
goto block_128;
}
else
{
uint8_t x_130; 
x_130 = l_Lean_instBEqFVarId_beq(x_1, x_100);
lean_dec(x_100);
x_103 = x_130;
goto block_128;
}
block_128:
{
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; uint8_t x_114; 
lean_dec(x_99);
lean_del_object(x_69);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_114 = !lean_is_exclusive(x_95);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_95, 0);
lean_dec(x_115);
x_104 = x_95;
x_105 = x_114;
goto block_113;
}
else
{
lean_dec(x_95);
x_104 = lean_box(0);
x_105 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_106; 
if (x_102 == 0)
{
lean_ctor_set_tag(x_101, 0);
lean_ctor_set(x_101, 1, x_20);
lean_ctor_set(x_101, 0, x_19);
x_106 = x_101;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_19);
lean_ctor_set(x_112, 1, x_20);
x_106 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_16);
lean_ctor_set(x_107, 1, x_106);
if (x_105 == 0)
{
lean_ctor_set(x_104, 0, x_107);
x_108 = x_104;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_107);
x_108 = x_110;
goto block_109;
}
block_109:
{
return x_108;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_del_object(x_101);
x_116 = lean_array_pop(x_16);
x_117 = lean_array_pop(x_116);
lean_inc(x_65);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_65);
x_119 = lean_array_set(x_20, x_99, x_118);
lean_dec(x_99);
x_120 = lean_array_push(x_19, x_95);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_dec_eq(x_66, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_nat_sub(x_66, x_121);
lean_dec(x_66);
if (x_70 == 0)
{
lean_ctor_set(x_69, 1, x_123);
x_124 = x_69;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(x_127, 0, x_65);
lean_ctor_set(x_127, 1, x_123);
lean_ctor_set_uint8(x_127, sizeof(void*)*2, x_67);
lean_ctor_set_uint8(x_127, sizeof(void*)*2 + 1, x_68);
x_124 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_125; 
x_125 = lean_array_push(x_120, x_124);
x_8 = x_119;
x_9 = x_117;
x_10 = x_125;
goto block_14;
}
}
else
{
lean_del_object(x_69);
lean_dec(x_66);
lean_dec(x_65);
x_8 = x_119;
x_9 = x_117;
x_10 = x_120;
goto block_14;
}
}
}
}
}
else
{
lean_dec(x_97);
lean_dec_ref(x_95);
lean_del_object(x_69);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_32 = lean_box(0);
goto block_36;
}
}
else
{
lean_dec(x_95);
lean_del_object(x_69);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_32 = lean_box(0);
goto block_36;
}
}
}
}
default: 
{
lean_dec(x_44);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_23 = lean_box(0);
goto block_31;
}
}
}
block_31:
{
lean_object* x_24; 
if (x_22 == 0)
{
x_24 = x_21;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_24);
x_25 = x_17;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_24);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_20);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0);
x_10 = lean_box(0);
x_11 = lean_mk_array(x_1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(x_2, x_13, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_35; 
x_15 = lean_ctor_get(x_14, 0);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
x_16 = x_14;
x_17 = x_35;
goto block_34;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_33; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
x_22 = x_18;
x_23 = x_33;
goto block_32;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Array_reverse___redArg(x_20);
x_25 = l_Array_append___redArg(x_19, x_24);
lean_dec_ref(x_24);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_25);
x_26 = x_22;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_21);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_26);
x_27 = x_16;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
x_36 = lean_ctor_get(x_14, 0);
x_43 = !lean_is_exclusive(x_14);
if (x_43 == 0)
{
x_37 = x_14;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_14);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = l_Lean_Expr_getAppFn(x_2);
x_8 = l_Lean_Expr_constName_x21(x_7);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3));
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6));
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__7, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__7);
x_14 = lean_array_push(x_13, x_10);
x_15 = lean_array_push(x_14, x_12);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_1);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(x_1, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(122u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0));
x_5 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
switch (lean_obj_tag(x_6)) {
case 3:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 2);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_6, 0);
lean_dec(x_24);
x_17 = x_6;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
lean_inc(x_1);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_1);
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
x_9 = x_19;
goto block_14;
}
}
}
case 5:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
x_25 = lean_ctor_get(x_6, 1);
x_26 = lean_ctor_get(x_6, 2);
x_27 = lean_ctor_get(x_6, 3);
x_28 = lean_ctor_get(x_6, 4);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_6, 0);
lean_dec(x_36);
x_29 = x_6;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
lean_inc(x_1);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_1);
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 2, x_26);
lean_ctor_set(x_33, 3, x_27);
lean_ctor_set(x_33, 4, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
x_9 = x_31;
goto block_14;
}
}
}
case 4:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
x_37 = lean_ctor_get(x_6, 1);
x_38 = lean_ctor_get(x_6, 2);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_6, 0);
lean_dec(x_46);
x_39 = x_6;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
lean_inc(x_1);
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_1);
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
x_9 = x_41;
goto block_14;
}
}
}
default: 
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_6);
x_47 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2);
x_48 = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(x_47);
x_9 = x_48;
goto block_14;
}
}
block_14:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(x_1, x_4, x_5, x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = 1;
x_11 = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(x_10, x_9, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_39; 
x_12 = lean_ctor_get(x_11, 0);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
x_13 = x_11;
x_14 = x_39;
goto block_38;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_39;
goto block_38;
}
block_38:
{
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
if (lean_obj_tag(x_15) == 6)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_nat_dec_eq(x_2, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_19 = lean_box(x_18);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_19);
x_20 = x_13;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_instBEqFVarId_beq(x_1, x_17);
lean_dec(x_17);
x_24 = lean_box(x_23);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_24);
x_25 = x_13;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_15);
x_28 = 0;
x_29 = lean_box(x_28);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_29);
x_30 = x_13;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_12);
x_33 = 0;
x_34 = lean_box(x_33);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_34);
x_35 = x_13;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
x_40 = lean_ctor_get(x_11, 0);
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
x_41 = x_11;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_11);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(x_1, x_2, x_3, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
x_7 = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(x_6, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_35; 
x_8 = lean_ctor_get(x_7, 0);
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
x_9 = x_7;
x_10 = x_35;
goto block_34;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_35;
goto block_34;
}
block_34:
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec_ref(x_8);
if (lean_obj_tag(x_11) == 7)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_nat_dec_eq(x_2, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_15 = lean_box(x_14);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_15);
x_16 = x_9;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_instBEqFVarId_beq(x_1, x_13);
lean_dec(x_13);
x_20 = lean_box(x_19);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_20);
x_21 = x_9;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
x_24 = 0;
x_25 = lean_box(x_24);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_25);
x_26 = x_9;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
x_29 = 0;
x_30 = lean_box(x_29);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_30);
x_31 = x_9;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
x_36 = lean_ctor_get(x_7, 0);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
x_37 = x_7;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_7);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(x_1, x_2, x_3, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(x_7, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_40; 
x_9 = lean_ctor_get(x_8, 0);
x_40 = !lean_is_exclusive(x_8);
if (x_40 == 0)
{
x_10 = x_8;
x_11 = x_40;
goto block_39;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_40;
goto block_39;
}
block_39:
{
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec_ref(x_9);
if (lean_obj_tag(x_12) == 8)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_27; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_dec_ref(x_12);
x_27 = lean_nat_dec_eq(x_2, x_13);
lean_dec(x_13);
if (x_27 == 0)
{
lean_dec(x_14);
x_16 = x_27;
goto block_26;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_eq(x_3, x_14);
lean_dec(x_14);
x_16 = x_28;
goto block_26;
}
block_26:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
x_17 = lean_box(x_16);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_17);
x_18 = x_10;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_instBEqFVarId_beq(x_1, x_15);
lean_dec(x_15);
x_22 = lean_box(x_21);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_22);
x_23 = x_10;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
x_29 = 0;
x_30 = lean_box(x_29);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_30);
x_31 = x_10;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_9);
x_34 = 0;
x_35 = lean_box(x_34);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_35);
x_36 = x_10;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
x_41 = lean_ctor_get(x_8, 0);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
x_42 = x_8;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(x_1, x_2, x_3, x_4, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_43; 
x_7 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
x_8 = l_ReaderT_instMonad___redArg(x_7);
x_9 = lean_ctor_get(x_8, 0);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_8, 1);
lean_dec(x_44);
x_10 = x_8;
x_11 = x_43;
goto block_42;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_40; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_9, 1);
lean_dec(x_41);
x_16 = x_9;
x_17 = x_40;
goto block_39;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
x_19 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_14);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_13);
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_23);
lean_ctor_set(x_16, 3, x_24);
lean_ctor_set(x_16, 2, x_25);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_22);
x_26 = x_16;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_22);
lean_ctor_set(x_38, 1, x_18);
lean_ctor_set(x_38, 2, x_25);
lean_ctor_set(x_38, 3, x_24);
lean_ctor_set(x_38, 4, x_23);
x_26 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_27; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_26);
x_27 = x_10;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_19);
x_27 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = l_instInhabitedOfMonad___redArg(x_28, x_30);
x_32 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_panic_fn(x_32, x_1);
x_34 = lean_apply_5(x_33, x_2, x_3, x_4, x_5, lean_box(0));
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(158u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0));
x_5 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_4, x_3);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_57; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
x_57 = !lean_is_exclusive(x_5);
if (x_57 == 0)
{
x_21 = x_5;
x_22 = x_57;
goto block_56;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_uget_borrowed(x_2, x_4);
switch (lean_obj_tag(x_23)) {
case 3:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_23, 1);
x_45 = lean_ctor_get(x_23, 2);
x_46 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(x_1, x_44, x_45, x_7);
x_24 = x_46;
goto block_43;
}
case 4:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 1);
x_48 = lean_ctor_get(x_23, 2);
x_49 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(x_1, x_47, x_48, x_7);
x_24 = x_49;
goto block_43;
}
case 5:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_23, 1);
x_51 = lean_ctor_get(x_23, 2);
x_52 = lean_ctor_get(x_23, 3);
x_53 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(x_1, x_50, x_51, x_52, x_7);
x_24 = x_53;
goto block_43;
}
default: 
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_55 = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(x_54, x_6, x_7, x_8, x_9);
x_24 = x_55;
goto block_43;
}
}
block_43:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_inc(x_23);
x_27 = lean_array_push(x_19, x_23);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_27);
x_28 = x_21;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_20);
x_28 = x_30;
goto block_29;
}
block_29:
{
x_11 = x_28;
x_12 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_inc(x_23);
x_31 = lean_array_push(x_20, x_23);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_31);
x_32 = x_21;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_11 = x_32;
x_12 = lean_box(0);
goto block_16;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_del_object(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_35 = lean_ctor_get(x_24, 0);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
x_36 = x_24;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0);
x_9 = lean_array_size(x_2);
x_10 = 0;
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(x_1, x_2, x_9, x_10, x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_28; 
x_12 = lean_ctor_get(x_11, 0);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
x_13 = x_11;
x_14 = x_28;
goto block_27;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_26; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
x_17 = x_12;
x_18 = x_26;
goto block_25;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_19; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 0, x_16);
x_19 = x_17;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_15);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_19);
x_20 = x_13;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
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
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
x_29 = lean_ctor_get(x_11, 0);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
x_30 = x_11;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
switch (lean_obj_tag(x_4)) {
case 7:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_23; 
x_5 = lean_ctor_get(x_2, 1);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_2, 0);
lean_dec(x_24);
x_6 = x_2;
x_7 = x_23;
goto block_22;
}
else
{
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 3);
x_10 = l_Lean_instBEqFVarId_beq(x_1, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
if (x_7 == 0)
{
x_11 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
x_11 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_9);
x_15 = 1;
x_16 = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(x_15, x_4);
lean_dec_ref(x_4);
x_17 = lean_array_push(x_5, x_16);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_17);
lean_ctor_set(x_6, 0, x_9);
x_18 = x_6;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_17);
x_18 = x_21;
goto block_20;
}
block_20:
{
x_2 = x_18;
goto _start;
}
}
}
}
case 9:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_43; 
x_25 = lean_ctor_get(x_2, 1);
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_2, 0);
lean_dec(x_44);
x_26 = x_2;
x_27 = x_43;
goto block_42;
}
else
{
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_box(0);
x_27 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 5);
x_30 = l_Lean_instBEqFVarId_beq(x_1, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
if (x_27 == 0)
{
x_31 = x_26;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_25);
x_31 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc_ref(x_29);
x_35 = 1;
x_36 = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(x_35, x_4);
lean_dec_ref(x_4);
x_37 = lean_array_push(x_25, x_36);
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_37);
lean_ctor_set(x_26, 0, x_29);
x_38 = x_26;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_37);
x_38 = x_41;
goto block_40;
}
block_40:
{
x_2 = x_38;
goto _start;
}
}
}
}
case 8:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_63; 
x_45 = lean_ctor_get(x_2, 1);
x_63 = !lean_is_exclusive(x_2);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_2, 0);
lean_dec(x_64);
x_46 = x_2;
x_47 = x_63;
goto block_62;
}
else
{
lean_inc(x_45);
lean_dec(x_2);
x_46 = lean_box(0);
x_47 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 3);
x_50 = l_Lean_instBEqFVarId_beq(x_1, x_48);
if (x_50 == 0)
{
lean_object* x_51; 
if (x_47 == 0)
{
x_51 = x_46;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_45);
x_51 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_inc_ref(x_49);
x_55 = 1;
x_56 = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(x_55, x_4);
lean_dec_ref(x_4);
x_57 = lean_array_push(x_45, x_56);
if (x_47 == 0)
{
lean_ctor_set(x_46, 1, x_57);
lean_ctor_set(x_46, 0, x_49);
x_58 = x_46;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_57);
x_58 = x_61;
goto block_60;
}
block_60:
{
x_2 = x_58;
goto _start;
}
}
}
}
default: 
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_73; 
x_65 = lean_ctor_get(x_2, 1);
x_73 = !lean_is_exclusive(x_2);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_2, 0);
lean_dec(x_74);
x_66 = x_2;
x_67 = x_73;
goto block_72;
}
else
{
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_box(0);
x_67 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_65);
x_68 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_27; 
x_11 = lean_ctor_get(x_10, 0);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
x_12 = x_10;
x_13 = x_27;
goto block_26;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_25; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
x_16 = x_11;
x_17 = x_25;
goto block_24;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 0, x_15);
x_18 = x_16;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_14);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_18);
x_19 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
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
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
x_28 = lean_ctor_get(x_10, 0);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
x_29 = x_10;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_4, x_1);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_array_fget_borrowed(x_2, x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1));
x_21 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_20, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = 1;
x_24 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(x_3);
lean_inc(x_4);
x_25 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_3);
x_26 = l_Lean_Compiler_LCNF_mkLetDecl(x_23, x_22, x_24, x_25, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 0);
x_29 = 0;
x_30 = lean_unsigned_to_nat(1u);
lean_inc(x_28);
x_31 = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_5);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
x_11 = x_32;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_ctor_get(x_26, 0);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
x_34 = x_26;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = lean_ctor_get(x_21, 0);
x_48 = !lean_is_exclusive(x_21);
if (x_48 == 0)
{
x_42 = x_21;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_21);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
x_11 = x_5;
x_12 = lean_box(0);
goto block_16;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_4 = x_14;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_2);
x_14 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___closed__0);
x_15 = lean_array_push(x_14, x_10);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(x_13, x_2, x_1, x_12, x_17, x_5, x_6, x_7, x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_array_uget_borrowed(x_1, x_3);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_unsigned_to_nat(1u);
x_17 = 0;
lean_inc(x_15);
x_18 = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_4);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_17);
x_6 = x_18;
x_7 = lean_box(0);
goto block_11;
}
else
{
x_6 = x_4;
x_7 = lean_box(0);
goto block_11;
}
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_4 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0);
x_12 = lean_array_push(x_11, x_10);
x_13 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = 1;
x_16 = 0;
x_17 = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 1, x_16);
x_18 = lean_array_size(x_2);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(x_2, x_18, x_19, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget_borrowed(x_2, x_5);
x_12 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(x_3, x_5, x_11, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_19 = lean_unbox(x_13);
lean_dec(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_4);
x_20 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 2, x_11);
lean_ctor_set(x_20, 3, x_6);
x_14 = x_20;
goto block_18;
}
else
{
x_14 = x_6;
goto block_18;
}
block_18:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_5 = x_16;
x_6 = x_14;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = lean_ctor_get(x_12, 0);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
x_22 = x_12;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_4);
x_15 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___closed__0);
x_16 = lean_array_push(x_15, x_12);
x_17 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_1);
x_18 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(x_14, x_4, x_6, x_1, x_13, x_17, x_8);
if (lean_obj_tag(x_18) == 0)
{
if (x_3 == 0)
{
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_28; 
x_19 = lean_ctor_get(x_18, 0);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
x_20 = x_18;
x_21 = x_28;
goto block_27;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_19);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_23);
x_24 = x_20;
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
else
{
lean_dec(x_1);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
x_13 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1));
x_12 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_11, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = 1;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
x_17 = l_Lean_Compiler_LCNF_mkLetDecl(x_15, x_13, x_14, x_16, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_34; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_19);
x_21 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(x_19, x_5);
x_22 = lean_ctor_get(x_21, 0);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
x_23 = x_21;
x_24 = x_34;
goto block_33;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___closed__0);
x_26 = lean_array_push(x_25, x_20);
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Compiler_LCNF_attachCodeDecls(x_15, x_22, x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_29);
x_30 = x_23;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec_ref(x_5);
lean_dec(x_4);
x_35 = lean_ctor_get(x_17, 0);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
x_36 = x_17;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_17);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_12, 0);
x_50 = !lean_is_exclusive(x_12);
if (x_50 == 0)
{
x_44 = x_12;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_12);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_28);
x_8 = x_28;
goto block_27;
}
case 1:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_29);
x_8 = x_29;
goto block_27;
}
default: 
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_30);
x_8 = x_30;
goto block_27;
}
}
block_27:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_2, x_8, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
x_10 = lean_ctor_get(x_9, 0);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
x_11 = x_9;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_1, x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_13);
x_14 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_9, 0);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_20 = x_9;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_7 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
x_8 = l_ReaderT_instMonad___redArg(x_7);
x_9 = lean_ctor_get(x_8, 0);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_8, 1);
lean_dec(x_43);
x_10 = x_8;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_39; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_9, 1);
lean_dec(x_40);
x_16 = x_9;
x_17 = x_39;
goto block_38;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
x_19 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_14);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_13);
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_23);
lean_ctor_set(x_16, 3, x_24);
lean_ctor_set(x_16, 2, x_25);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_22);
x_26 = x_16;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_18);
lean_ctor_set(x_37, 2, x_25);
lean_ctor_set(x_37, 3, x_24);
lean_ctor_set(x_37, 4, x_23);
x_26 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_27; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_26);
x_27 = x_10;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_19);
x_27 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0);
x_30 = l_instInhabitedOfMonad___redArg(x_28, x_29);
x_31 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_panic_fn(x_31, x_1);
x_33 = lean_apply_5(x_32, x_2, x_3, x_4, x_5, lean_box(0));
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed), 10, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
x_16 = lean_array_fget_borrowed(x_6, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_16);
x_17 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(x_16, x_15, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ptr_addr(x_16);
x_20 = lean_ptr_addr(x_18);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
x_24 = lean_array_fset(x_6, x_5, x_18);
lean_dec(x_5);
x_5 = x_23;
x_6 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_27;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_17, 0);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
x_30 = x_17;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7));
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(192u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6));
x_5 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 12)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_135; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 2);
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_20 = lean_ctor_get(x_12, 2);
x_135 = !lean_is_exclusive(x_12);
if (x_135 == 0)
{
x_21 = x_12;
x_22 = x_135;
goto block_134;
}
else
{
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = x_135;
goto block_134;
}
block_134:
{
uint8_t x_23; 
x_23 = l_Lean_instBEqFVarId_beq(x_1, x_17);
lean_dec(x_17);
if (x_23 == 0)
{
lean_object* x_24; 
lean_del_object(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
lean_inc_ref(x_13);
x_24 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_47; 
x_25 = lean_ctor_get(x_24, 0);
x_47 = !lean_is_exclusive(x_24);
if (x_47 == 0)
{
x_26 = x_24;
x_27 = x_47;
goto block_46;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_47;
goto block_46;
}
block_46:
{
size_t x_28; size_t x_29; uint8_t x_30; 
x_28 = lean_ptr_addr(x_13);
x_29 = lean_ptr_addr(x_25);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; uint8_t x_40; 
lean_inc_ref(x_11);
x_40 = !lean_is_exclusive(x_2);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_2, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_2, 0);
lean_dec(x_42);
x_31 = x_2;
x_32 = x_40;
goto block_39;
}
else
{
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_33; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_25);
x_33 = x_31;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_25);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_33);
x_34 = x_26;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_2);
x_43 = x_26;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_2);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
else
{
lean_dec_ref(x_2);
return x_24;
}
}
else
{
lean_object* x_48; uint8_t x_49; uint8_t x_131; 
lean_inc_ref(x_13);
lean_inc_ref(x_11);
x_131 = !lean_is_exclusive(x_2);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_2, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_2, 0);
lean_dec(x_133);
x_48 = x_2;
x_49 = x_131;
goto block_130;
}
else
{
lean_dec(x_2);
x_48 = lean_box(0);
x_49 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_50; 
x_50 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(x_14, x_13, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_54 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(x_3, x_52, x_6, x_7, x_8, x_9);
lean_dec(x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1));
x_59 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_58, x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = 1;
x_62 = l_Lean_Compiler_LCNF_attachCodeDecls(x_61, x_57, x_53);
lean_dec(x_57);
x_63 = 0;
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
if (x_22 == 0)
{
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 0, x_14);
x_64 = x_21;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_105, 0, x_14);
lean_ctor_set(x_105, 1, x_15);
lean_ctor_set(x_105, 2, x_16);
x_64 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_63);
x_65 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2);
x_66 = lean_array_push(x_65, x_64);
lean_inc_ref(x_5);
x_67 = l_Lean_Compiler_LCNF_mkFunDecl(x_61, x_60, x_5, x_66, x_62, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_inc_ref(x_20);
lean_inc_ref(x_18);
lean_inc_ref(x_11);
x_70 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(x_11, x_18, x_20, x_69, x_56, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
lean_inc(x_69);
x_72 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(x_1, x_18, x_19, x_20, x_69, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_61, x_11, x_7);
lean_dec(x_7);
lean_dec_ref(x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_74);
x_75 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5);
x_76 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(x_4, x_75, x_5, x_71, x_73);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_87; 
x_77 = lean_ctor_get(x_76, 0);
x_87 = !lean_is_exclusive(x_76);
if (x_87 == 0)
{
x_78 = x_76;
x_79 = x_87;
goto block_86;
}
else
{
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_box(0);
x_79 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_80; 
if (x_49 == 0)
{
lean_ctor_set_tag(x_48, 2);
lean_ctor_set(x_48, 1, x_77);
lean_ctor_set(x_48, 0, x_68);
x_80 = x_48;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_68);
lean_ctor_set(x_85, 1, x_77);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_79 == 0)
{
lean_ctor_set(x_78, 0, x_80);
x_81 = x_78;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_80);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
else
{
lean_dec(x_68);
lean_del_object(x_48);
return x_76;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_68);
lean_del_object(x_48);
lean_dec_ref(x_5);
lean_dec(x_4);
x_88 = lean_ctor_get(x_74, 0);
x_95 = !lean_is_exclusive(x_74);
if (x_95 == 0)
{
x_89 = x_74;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_74);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
else
{
lean_dec(x_71);
lean_dec(x_68);
lean_del_object(x_48);
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_72;
}
}
else
{
lean_dec(x_68);
lean_del_object(x_48);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_70;
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_103; 
lean_dec(x_56);
lean_del_object(x_48);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_96 = lean_ctor_get(x_67, 0);
x_103 = !lean_is_exclusive(x_67);
if (x_103 == 0)
{
x_97 = x_67;
x_98 = x_103;
goto block_102;
}
else
{
lean_inc(x_96);
lean_dec(x_67);
x_97 = lean_box(0);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_98 == 0)
{
x_99 = x_97;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_96);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_113; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_53);
lean_del_object(x_48);
lean_del_object(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_106 = lean_ctor_get(x_59, 0);
x_113 = !lean_is_exclusive(x_59);
if (x_113 == 0)
{
x_107 = x_59;
x_108 = x_113;
goto block_112;
}
else
{
lean_inc(x_106);
lean_dec(x_59);
x_107 = lean_box(0);
x_108 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_109; 
if (x_108 == 0)
{
x_109 = x_107;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_106);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_121; 
lean_dec(x_53);
lean_del_object(x_48);
lean_del_object(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_114 = lean_ctor_get(x_54, 0);
x_121 = !lean_is_exclusive(x_54);
if (x_121 == 0)
{
x_115 = x_54;
x_116 = x_121;
goto block_120;
}
else
{
lean_inc(x_114);
lean_dec(x_54);
x_115 = lean_box(0);
x_116 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_117; 
if (x_116 == 0)
{
x_117 = x_115;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_114);
x_117 = x_119;
goto block_118;
}
block_118:
{
return x_117;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_129; 
lean_del_object(x_48);
lean_del_object(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_122 = lean_ctor_get(x_50, 0);
x_129 = !lean_is_exclusive(x_50);
if (x_129 == 0)
{
x_123 = x_50;
x_124 = x_129;
goto block_128;
}
else
{
lean_inc(x_122);
lean_dec(x_50);
x_123 = lean_box(0);
x_124 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_125; 
if (x_124 == 0)
{
x_125 = x_123;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_122);
x_125 = x_127;
goto block_126;
}
block_126:
{
return x_125;
}
}
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_12);
x_136 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_136);
x_137 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_136, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_160; 
x_138 = lean_ctor_get(x_137, 0);
x_160 = !lean_is_exclusive(x_137);
if (x_160 == 0)
{
x_139 = x_137;
x_140 = x_160;
goto block_159;
}
else
{
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_box(0);
x_140 = x_160;
goto block_159;
}
block_159:
{
size_t x_141; size_t x_142; uint8_t x_143; 
x_141 = lean_ptr_addr(x_136);
x_142 = lean_ptr_addr(x_138);
x_143 = lean_usize_dec_eq(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; uint8_t x_153; 
lean_inc_ref(x_11);
x_153 = !lean_is_exclusive(x_2);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_2, 1);
lean_dec(x_154);
x_155 = lean_ctor_get(x_2, 0);
lean_dec(x_155);
x_144 = x_2;
x_145 = x_153;
goto block_152;
}
else
{
lean_dec(x_2);
x_144 = lean_box(0);
x_145 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_146; 
if (x_145 == 0)
{
lean_ctor_set(x_144, 1, x_138);
x_146 = x_144;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_11);
lean_ctor_set(x_151, 1, x_138);
x_146 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_147; 
if (x_140 == 0)
{
lean_ctor_set(x_139, 0, x_146);
x_147 = x_139;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_146);
x_147 = x_149;
goto block_148;
}
block_148:
{
return x_147;
}
}
}
}
else
{
lean_object* x_156; 
lean_dec(x_138);
if (x_140 == 0)
{
lean_ctor_set(x_139, 0, x_2);
x_156 = x_139;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_2);
x_156 = x_158;
goto block_157;
}
block_157:
{
return x_156;
}
}
}
}
else
{
lean_dec_ref(x_2);
return x_137;
}
}
}
case 2:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_ctor_get(x_2, 0);
x_162 = lean_ctor_get(x_2, 1);
x_163 = lean_ctor_get(x_161, 2);
x_164 = lean_ctor_get(x_161, 3);
x_165 = lean_ctor_get(x_161, 4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_164);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_165);
lean_inc(x_1);
x_166 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_165, x_3, x_4, x_164, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; uint8_t x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
x_168 = 1;
lean_inc_ref(x_163);
lean_inc_ref(x_164);
lean_inc_ref(x_161);
x_169 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_168, x_161, x_164, x_163, x_167, x_7);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
lean_inc_ref(x_162);
x_171 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_162, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_199; 
x_172 = lean_ctor_get(x_171, 0);
x_199 = !lean_is_exclusive(x_171);
if (x_199 == 0)
{
x_173 = x_171;
x_174 = x_199;
goto block_198;
}
else
{
lean_inc(x_172);
lean_dec(x_171);
x_173 = lean_box(0);
x_174 = x_199;
goto block_198;
}
block_198:
{
uint8_t x_175; size_t x_192; size_t x_193; uint8_t x_194; 
x_192 = lean_ptr_addr(x_162);
x_193 = lean_ptr_addr(x_172);
x_194 = lean_usize_dec_eq(x_192, x_193);
if (x_194 == 0)
{
x_175 = x_194;
goto block_191;
}
else
{
size_t x_195; size_t x_196; uint8_t x_197; 
x_195 = lean_ptr_addr(x_161);
x_196 = lean_ptr_addr(x_170);
x_197 = lean_usize_dec_eq(x_195, x_196);
x_175 = x_197;
goto block_191;
}
block_191:
{
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; uint8_t x_185; 
x_185 = !lean_is_exclusive(x_2);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_2, 1);
lean_dec(x_186);
x_187 = lean_ctor_get(x_2, 0);
lean_dec(x_187);
x_176 = x_2;
x_177 = x_185;
goto block_184;
}
else
{
lean_dec(x_2);
x_176 = lean_box(0);
x_177 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_178; 
if (x_177 == 0)
{
lean_ctor_set(x_176, 1, x_172);
lean_ctor_set(x_176, 0, x_170);
x_178 = x_176;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_183, 0, x_170);
lean_ctor_set(x_183, 1, x_172);
x_178 = x_183;
goto block_182;
}
block_182:
{
lean_object* x_179; 
if (x_174 == 0)
{
lean_ctor_set(x_173, 0, x_178);
x_179 = x_173;
goto block_180;
}
else
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_178);
x_179 = x_181;
goto block_180;
}
block_180:
{
return x_179;
}
}
}
}
else
{
lean_object* x_188; 
lean_dec(x_172);
lean_dec(x_170);
if (x_174 == 0)
{
lean_ctor_set(x_173, 0, x_2);
x_188 = x_173;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_2);
x_188 = x_190;
goto block_189;
}
block_189:
{
return x_188;
}
}
}
}
}
else
{
lean_dec(x_170);
lean_dec_ref(x_2);
return x_171;
}
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_207; 
lean_dec_ref(x_2);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_200 = lean_ctor_get(x_169, 0);
x_207 = !lean_is_exclusive(x_169);
if (x_207 == 0)
{
x_201 = x_169;
x_202 = x_207;
goto block_206;
}
else
{
lean_inc(x_200);
lean_dec(x_169);
x_201 = lean_box(0);
x_202 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_203; 
if (x_202 == 0)
{
x_203 = x_201;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_200);
x_203 = x_205;
goto block_204;
}
block_204:
{
return x_203;
}
}
}
}
else
{
lean_dec_ref(x_2);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_166;
}
}
case 4:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_251; 
lean_dec_ref(x_5);
x_208 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_208, 0);
x_210 = lean_ctor_get(x_208, 1);
x_211 = lean_ctor_get(x_208, 2);
x_212 = lean_ctor_get(x_208, 3);
x_251 = !lean_is_exclusive(x_208);
if (x_251 == 0)
{
x_213 = x_208;
x_214 = x_251;
goto block_250;
}
else
{
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_208);
x_213 = lean_box(0);
x_214 = x_251;
goto block_250;
}
block_250:
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_212);
lean_inc_ref(x_210);
x_216 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(x_1, x_3, x_4, x_210, x_215, x_212, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; uint8_t x_241; 
x_217 = lean_ctor_get(x_216, 0);
x_241 = !lean_is_exclusive(x_216);
if (x_241 == 0)
{
x_218 = x_216;
x_219 = x_241;
goto block_240;
}
else
{
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_box(0);
x_219 = x_241;
goto block_240;
}
block_240:
{
size_t x_220; size_t x_221; uint8_t x_222; 
x_220 = lean_ptr_addr(x_212);
lean_dec_ref(x_212);
x_221 = lean_ptr_addr(x_217);
x_222 = lean_usize_dec_eq(x_220, x_221);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; uint8_t x_235; 
x_235 = !lean_is_exclusive(x_2);
if (x_235 == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_2, 0);
lean_dec(x_236);
x_223 = x_2;
x_224 = x_235;
goto block_234;
}
else
{
lean_dec(x_2);
x_223 = lean_box(0);
x_224 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_225; 
if (x_214 == 0)
{
lean_ctor_set(x_213, 3, x_217);
x_225 = x_213;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_233, 0, x_209);
lean_ctor_set(x_233, 1, x_210);
lean_ctor_set(x_233, 2, x_211);
lean_ctor_set(x_233, 3, x_217);
x_225 = x_233;
goto block_232;
}
block_232:
{
lean_object* x_226; 
if (x_224 == 0)
{
lean_ctor_set(x_223, 0, x_225);
x_226 = x_223;
goto block_230;
}
else
{
lean_object* x_231; 
x_231 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_231, 0, x_225);
x_226 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_227; 
if (x_219 == 0)
{
lean_ctor_set(x_218, 0, x_226);
x_227 = x_218;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_226);
x_227 = x_229;
goto block_228;
}
block_228:
{
return x_227;
}
}
}
}
}
else
{
lean_object* x_237; 
lean_dec(x_217);
lean_del_object(x_213);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec(x_209);
if (x_219 == 0)
{
lean_ctor_set(x_218, 0, x_2);
x_237 = x_218;
goto block_238;
}
else
{
lean_object* x_239; 
x_239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_239, 0, x_2);
x_237 = x_239;
goto block_238;
}
block_238:
{
return x_237;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_249; 
lean_del_object(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec(x_209);
lean_dec_ref(x_2);
x_242 = lean_ctor_get(x_216, 0);
x_249 = !lean_is_exclusive(x_216);
if (x_249 == 0)
{
x_243 = x_216;
x_244 = x_249;
goto block_248;
}
else
{
lean_inc(x_242);
lean_dec(x_216);
x_243 = lean_box(0);
x_244 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_245; 
if (x_244 == 0)
{
x_245 = x_243;
goto block_246;
}
else
{
lean_object* x_247; 
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_242);
x_245 = x_247;
goto block_246;
}
block_246:
{
return x_245;
}
}
}
}
}
case 7:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_2, 0);
x_253 = lean_ctor_get(x_2, 1);
x_254 = lean_ctor_get(x_2, 2);
x_255 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_255);
x_256 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_255, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; uint8_t x_281; 
x_257 = lean_ctor_get(x_256, 0);
x_281 = !lean_is_exclusive(x_256);
if (x_281 == 0)
{
x_258 = x_256;
x_259 = x_281;
goto block_280;
}
else
{
lean_inc(x_257);
lean_dec(x_256);
x_258 = lean_box(0);
x_259 = x_281;
goto block_280;
}
block_280:
{
size_t x_260; size_t x_261; uint8_t x_262; 
x_260 = lean_ptr_addr(x_255);
x_261 = lean_ptr_addr(x_257);
x_262 = lean_usize_dec_eq(x_260, x_261);
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; uint8_t x_272; 
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
x_272 = !lean_is_exclusive(x_2);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_2, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_2, 2);
lean_dec(x_274);
x_275 = lean_ctor_get(x_2, 1);
lean_dec(x_275);
x_276 = lean_ctor_get(x_2, 0);
lean_dec(x_276);
x_263 = x_2;
x_264 = x_272;
goto block_271;
}
else
{
lean_dec(x_2);
x_263 = lean_box(0);
x_264 = x_272;
goto block_271;
}
block_271:
{
lean_object* x_265; 
if (x_264 == 0)
{
lean_ctor_set(x_263, 3, x_257);
x_265 = x_263;
goto block_269;
}
else
{
lean_object* x_270; 
x_270 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_270, 0, x_252);
lean_ctor_set(x_270, 1, x_253);
lean_ctor_set(x_270, 2, x_254);
lean_ctor_set(x_270, 3, x_257);
x_265 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_266; 
if (x_259 == 0)
{
lean_ctor_set(x_258, 0, x_265);
x_266 = x_258;
goto block_267;
}
else
{
lean_object* x_268; 
x_268 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_268, 0, x_265);
x_266 = x_268;
goto block_267;
}
block_267:
{
return x_266;
}
}
}
}
else
{
lean_object* x_277; 
lean_dec(x_257);
if (x_259 == 0)
{
lean_ctor_set(x_258, 0, x_2);
x_277 = x_258;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_279, 0, x_2);
x_277 = x_279;
goto block_278;
}
block_278:
{
return x_277;
}
}
}
}
else
{
lean_dec_ref(x_2);
return x_256;
}
}
case 8:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_2, 0);
x_283 = lean_ctor_get(x_2, 1);
x_284 = lean_ctor_get(x_2, 2);
x_285 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_285);
x_286 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_285, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_311; 
x_287 = lean_ctor_get(x_286, 0);
x_311 = !lean_is_exclusive(x_286);
if (x_311 == 0)
{
x_288 = x_286;
x_289 = x_311;
goto block_310;
}
else
{
lean_inc(x_287);
lean_dec(x_286);
x_288 = lean_box(0);
x_289 = x_311;
goto block_310;
}
block_310:
{
size_t x_290; size_t x_291; uint8_t x_292; 
x_290 = lean_ptr_addr(x_285);
x_291 = lean_ptr_addr(x_287);
x_292 = lean_usize_dec_eq(x_290, x_291);
if (x_292 == 0)
{
lean_object* x_293; uint8_t x_294; uint8_t x_302; 
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
x_302 = !lean_is_exclusive(x_2);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_303 = lean_ctor_get(x_2, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_2, 2);
lean_dec(x_304);
x_305 = lean_ctor_get(x_2, 1);
lean_dec(x_305);
x_306 = lean_ctor_get(x_2, 0);
lean_dec(x_306);
x_293 = x_2;
x_294 = x_302;
goto block_301;
}
else
{
lean_dec(x_2);
x_293 = lean_box(0);
x_294 = x_302;
goto block_301;
}
block_301:
{
lean_object* x_295; 
if (x_294 == 0)
{
lean_ctor_set(x_293, 3, x_287);
x_295 = x_293;
goto block_299;
}
else
{
lean_object* x_300; 
x_300 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_300, 0, x_282);
lean_ctor_set(x_300, 1, x_283);
lean_ctor_set(x_300, 2, x_284);
lean_ctor_set(x_300, 3, x_287);
x_295 = x_300;
goto block_299;
}
block_299:
{
lean_object* x_296; 
if (x_289 == 0)
{
lean_ctor_set(x_288, 0, x_295);
x_296 = x_288;
goto block_297;
}
else
{
lean_object* x_298; 
x_298 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_298, 0, x_295);
x_296 = x_298;
goto block_297;
}
block_297:
{
return x_296;
}
}
}
}
else
{
lean_object* x_307; 
lean_dec(x_287);
if (x_289 == 0)
{
lean_ctor_set(x_288, 0, x_2);
x_307 = x_288;
goto block_308;
}
else
{
lean_object* x_309; 
x_309 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_309, 0, x_2);
x_307 = x_309;
goto block_308;
}
block_308:
{
return x_307;
}
}
}
}
else
{
lean_dec_ref(x_2);
return x_286;
}
}
case 9:
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_312 = lean_ctor_get(x_2, 0);
x_313 = lean_ctor_get(x_2, 1);
x_314 = lean_ctor_get(x_2, 2);
x_315 = lean_ctor_get(x_2, 3);
x_316 = lean_ctor_get(x_2, 4);
x_317 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_317);
x_318 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_317, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; uint8_t x_345; 
x_319 = lean_ctor_get(x_318, 0);
x_345 = !lean_is_exclusive(x_318);
if (x_345 == 0)
{
x_320 = x_318;
x_321 = x_345;
goto block_344;
}
else
{
lean_inc(x_319);
lean_dec(x_318);
x_320 = lean_box(0);
x_321 = x_345;
goto block_344;
}
block_344:
{
size_t x_322; size_t x_323; uint8_t x_324; 
x_322 = lean_ptr_addr(x_317);
x_323 = lean_ptr_addr(x_319);
x_324 = lean_usize_dec_eq(x_322, x_323);
if (x_324 == 0)
{
lean_object* x_325; uint8_t x_326; uint8_t x_334; 
lean_inc_ref(x_316);
lean_inc(x_315);
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_312);
x_334 = !lean_is_exclusive(x_2);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_335 = lean_ctor_get(x_2, 5);
lean_dec(x_335);
x_336 = lean_ctor_get(x_2, 4);
lean_dec(x_336);
x_337 = lean_ctor_get(x_2, 3);
lean_dec(x_337);
x_338 = lean_ctor_get(x_2, 2);
lean_dec(x_338);
x_339 = lean_ctor_get(x_2, 1);
lean_dec(x_339);
x_340 = lean_ctor_get(x_2, 0);
lean_dec(x_340);
x_325 = x_2;
x_326 = x_334;
goto block_333;
}
else
{
lean_dec(x_2);
x_325 = lean_box(0);
x_326 = x_334;
goto block_333;
}
block_333:
{
lean_object* x_327; 
if (x_326 == 0)
{
lean_ctor_set(x_325, 5, x_319);
x_327 = x_325;
goto block_331;
}
else
{
lean_object* x_332; 
x_332 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_332, 0, x_312);
lean_ctor_set(x_332, 1, x_313);
lean_ctor_set(x_332, 2, x_314);
lean_ctor_set(x_332, 3, x_315);
lean_ctor_set(x_332, 4, x_316);
lean_ctor_set(x_332, 5, x_319);
x_327 = x_332;
goto block_331;
}
block_331:
{
lean_object* x_328; 
if (x_321 == 0)
{
lean_ctor_set(x_320, 0, x_327);
x_328 = x_320;
goto block_329;
}
else
{
lean_object* x_330; 
x_330 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_330, 0, x_327);
x_328 = x_330;
goto block_329;
}
block_329:
{
return x_328;
}
}
}
}
else
{
lean_object* x_341; 
lean_dec(x_319);
if (x_321 == 0)
{
lean_ctor_set(x_320, 0, x_2);
x_341 = x_320;
goto block_342;
}
else
{
lean_object* x_343; 
x_343 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_343, 0, x_2);
x_341 = x_343;
goto block_342;
}
block_342:
{
return x_341;
}
}
}
}
else
{
lean_dec_ref(x_2);
return x_318;
}
}
case 10:
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_ctor_get(x_2, 0);
x_347 = lean_ctor_get(x_2, 1);
x_348 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_348);
x_349 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_348, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_373; 
x_350 = lean_ctor_get(x_349, 0);
x_373 = !lean_is_exclusive(x_349);
if (x_373 == 0)
{
x_351 = x_349;
x_352 = x_373;
goto block_372;
}
else
{
lean_inc(x_350);
lean_dec(x_349);
x_351 = lean_box(0);
x_352 = x_373;
goto block_372;
}
block_372:
{
size_t x_353; size_t x_354; uint8_t x_355; 
x_353 = lean_ptr_addr(x_348);
x_354 = lean_ptr_addr(x_350);
x_355 = lean_usize_dec_eq(x_353, x_354);
if (x_355 == 0)
{
lean_object* x_356; uint8_t x_357; uint8_t x_365; 
lean_inc(x_347);
lean_inc(x_346);
x_365 = !lean_is_exclusive(x_2);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_2, 2);
lean_dec(x_366);
x_367 = lean_ctor_get(x_2, 1);
lean_dec(x_367);
x_368 = lean_ctor_get(x_2, 0);
lean_dec(x_368);
x_356 = x_2;
x_357 = x_365;
goto block_364;
}
else
{
lean_dec(x_2);
x_356 = lean_box(0);
x_357 = x_365;
goto block_364;
}
block_364:
{
lean_object* x_358; 
if (x_357 == 0)
{
lean_ctor_set(x_356, 2, x_350);
x_358 = x_356;
goto block_362;
}
else
{
lean_object* x_363; 
x_363 = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(x_363, 0, x_346);
lean_ctor_set(x_363, 1, x_347);
lean_ctor_set(x_363, 2, x_350);
x_358 = x_363;
goto block_362;
}
block_362:
{
lean_object* x_359; 
if (x_352 == 0)
{
lean_ctor_set(x_351, 0, x_358);
x_359 = x_351;
goto block_360;
}
else
{
lean_object* x_361; 
x_361 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_361, 0, x_358);
x_359 = x_361;
goto block_360;
}
block_360:
{
return x_359;
}
}
}
}
else
{
lean_object* x_369; 
lean_dec(x_350);
if (x_352 == 0)
{
lean_ctor_set(x_351, 0, x_2);
x_369 = x_351;
goto block_370;
}
else
{
lean_object* x_371; 
x_371 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_371, 0, x_2);
x_369 = x_371;
goto block_370;
}
block_370:
{
return x_369;
}
}
}
}
else
{
lean_dec_ref(x_2);
return x_349;
}
}
case 11:
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; 
x_374 = lean_ctor_get(x_2, 0);
x_375 = lean_ctor_get(x_2, 1);
x_376 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_377 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_378 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_378);
x_379 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_378, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_403; 
x_380 = lean_ctor_get(x_379, 0);
x_403 = !lean_is_exclusive(x_379);
if (x_403 == 0)
{
x_381 = x_379;
x_382 = x_403;
goto block_402;
}
else
{
lean_inc(x_380);
lean_dec(x_379);
x_381 = lean_box(0);
x_382 = x_403;
goto block_402;
}
block_402:
{
size_t x_383; size_t x_384; uint8_t x_385; 
x_383 = lean_ptr_addr(x_378);
x_384 = lean_ptr_addr(x_380);
x_385 = lean_usize_dec_eq(x_383, x_384);
if (x_385 == 0)
{
lean_object* x_386; uint8_t x_387; uint8_t x_395; 
lean_inc(x_375);
lean_inc(x_374);
x_395 = !lean_is_exclusive(x_2);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_2, 2);
lean_dec(x_396);
x_397 = lean_ctor_get(x_2, 1);
lean_dec(x_397);
x_398 = lean_ctor_get(x_2, 0);
lean_dec(x_398);
x_386 = x_2;
x_387 = x_395;
goto block_394;
}
else
{
lean_dec(x_2);
x_386 = lean_box(0);
x_387 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_388; 
if (x_387 == 0)
{
lean_ctor_set(x_386, 2, x_380);
x_388 = x_386;
goto block_392;
}
else
{
lean_object* x_393; 
x_393 = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(x_393, 0, x_374);
lean_ctor_set(x_393, 1, x_375);
lean_ctor_set(x_393, 2, x_380);
lean_ctor_set_uint8(x_393, sizeof(void*)*3, x_376);
lean_ctor_set_uint8(x_393, sizeof(void*)*3 + 1, x_377);
x_388 = x_393;
goto block_392;
}
block_392:
{
lean_object* x_389; 
if (x_382 == 0)
{
lean_ctor_set(x_381, 0, x_388);
x_389 = x_381;
goto block_390;
}
else
{
lean_object* x_391; 
x_391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_391, 0, x_388);
x_389 = x_391;
goto block_390;
}
block_390:
{
return x_389;
}
}
}
}
else
{
lean_object* x_399; 
lean_dec(x_380);
if (x_382 == 0)
{
lean_ctor_set(x_381, 0, x_2);
x_399 = x_381;
goto block_400;
}
else
{
lean_object* x_401; 
x_401 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_401, 0, x_2);
x_399 = x_401;
goto block_400;
}
block_400:
{
return x_399;
}
}
}
}
else
{
lean_dec_ref(x_2);
return x_379;
}
}
case 12:
{
lean_object* x_404; lean_object* x_405; uint8_t x_406; uint8_t x_407; lean_object* x_408; uint8_t x_409; 
x_404 = lean_ctor_get(x_2, 0);
x_405 = lean_ctor_get(x_2, 1);
x_406 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_407 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_408 = lean_ctor_get(x_2, 2);
x_409 = l_Lean_instBEqFVarId_beq(x_1, x_404);
if (x_409 == 0)
{
lean_object* x_410; 
lean_inc_ref(x_408);
x_410 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_408, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; uint8_t x_413; uint8_t x_434; 
x_411 = lean_ctor_get(x_410, 0);
x_434 = !lean_is_exclusive(x_410);
if (x_434 == 0)
{
x_412 = x_410;
x_413 = x_434;
goto block_433;
}
else
{
lean_inc(x_411);
lean_dec(x_410);
x_412 = lean_box(0);
x_413 = x_434;
goto block_433;
}
block_433:
{
size_t x_414; size_t x_415; uint8_t x_416; 
x_414 = lean_ptr_addr(x_408);
x_415 = lean_ptr_addr(x_411);
x_416 = lean_usize_dec_eq(x_414, x_415);
if (x_416 == 0)
{
lean_object* x_417; uint8_t x_418; uint8_t x_426; 
lean_inc(x_405);
lean_inc(x_404);
x_426 = !lean_is_exclusive(x_2);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_2, 2);
lean_dec(x_427);
x_428 = lean_ctor_get(x_2, 1);
lean_dec(x_428);
x_429 = lean_ctor_get(x_2, 0);
lean_dec(x_429);
x_417 = x_2;
x_418 = x_426;
goto block_425;
}
else
{
lean_dec(x_2);
x_417 = lean_box(0);
x_418 = x_426;
goto block_425;
}
block_425:
{
lean_object* x_419; 
if (x_418 == 0)
{
lean_ctor_set(x_417, 2, x_411);
x_419 = x_417;
goto block_423;
}
else
{
lean_object* x_424; 
x_424 = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(x_424, 0, x_404);
lean_ctor_set(x_424, 1, x_405);
lean_ctor_set(x_424, 2, x_411);
lean_ctor_set_uint8(x_424, sizeof(void*)*3, x_406);
lean_ctor_set_uint8(x_424, sizeof(void*)*3 + 1, x_407);
x_419 = x_424;
goto block_423;
}
block_423:
{
lean_object* x_420; 
if (x_413 == 0)
{
lean_ctor_set(x_412, 0, x_419);
x_420 = x_412;
goto block_421;
}
else
{
lean_object* x_422; 
x_422 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_422, 0, x_419);
x_420 = x_422;
goto block_421;
}
block_421:
{
return x_420;
}
}
}
}
else
{
lean_object* x_430; 
lean_dec(x_411);
if (x_413 == 0)
{
lean_ctor_set(x_412, 0, x_2);
x_430 = x_412;
goto block_431;
}
else
{
lean_object* x_432; 
x_432 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_432, 0, x_2);
x_430 = x_432;
goto block_431;
}
block_431:
{
return x_430;
}
}
}
}
else
{
lean_dec_ref(x_2);
return x_410;
}
}
else
{
lean_object* x_435; uint8_t x_436; 
lean_inc_ref(x_408);
lean_inc(x_405);
lean_dec_ref(x_2);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_435 = lean_unsigned_to_nat(1u);
x_436 = lean_nat_dec_eq(x_405, x_435);
lean_dec(x_405);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; 
lean_dec_ref(x_408);
lean_dec(x_1);
x_437 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__8, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__8);
x_438 = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(x_437, x_6, x_7, x_8, x_9);
return x_438;
}
else
{
lean_object* x_439; lean_object* x_440; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_439 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_439, 0, x_1);
lean_ctor_set(x_439, 1, x_408);
x_440 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_440, 0, x_439);
return x_440;
}
}
}
case 13:
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_2, 0);
x_442 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_442);
x_443 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_442, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; uint8_t x_446; uint8_t x_466; 
x_444 = lean_ctor_get(x_443, 0);
x_466 = !lean_is_exclusive(x_443);
if (x_466 == 0)
{
x_445 = x_443;
x_446 = x_466;
goto block_465;
}
else
{
lean_inc(x_444);
lean_dec(x_443);
x_445 = lean_box(0);
x_446 = x_466;
goto block_465;
}
block_465:
{
size_t x_447; size_t x_448; uint8_t x_449; 
x_447 = lean_ptr_addr(x_442);
x_448 = lean_ptr_addr(x_444);
x_449 = lean_usize_dec_eq(x_447, x_448);
if (x_449 == 0)
{
lean_object* x_450; uint8_t x_451; uint8_t x_459; 
lean_inc(x_441);
x_459 = !lean_is_exclusive(x_2);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_ctor_get(x_2, 1);
lean_dec(x_460);
x_461 = lean_ctor_get(x_2, 0);
lean_dec(x_461);
x_450 = x_2;
x_451 = x_459;
goto block_458;
}
else
{
lean_dec(x_2);
x_450 = lean_box(0);
x_451 = x_459;
goto block_458;
}
block_458:
{
lean_object* x_452; 
if (x_451 == 0)
{
lean_ctor_set(x_450, 1, x_444);
x_452 = x_450;
goto block_456;
}
else
{
lean_object* x_457; 
x_457 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_457, 0, x_441);
lean_ctor_set(x_457, 1, x_444);
x_452 = x_457;
goto block_456;
}
block_456:
{
lean_object* x_453; 
if (x_446 == 0)
{
lean_ctor_set(x_445, 0, x_452);
x_453 = x_445;
goto block_454;
}
else
{
lean_object* x_455; 
x_455 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_455, 0, x_452);
x_453 = x_455;
goto block_454;
}
block_454:
{
return x_453;
}
}
}
}
else
{
lean_object* x_462; 
lean_dec(x_444);
if (x_446 == 0)
{
lean_ctor_set(x_445, 0, x_2);
x_462 = x_445;
goto block_463;
}
else
{
lean_object* x_464; 
x_464 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_464, 0, x_2);
x_462 = x_464;
goto block_463;
}
block_463:
{
return x_462;
}
}
}
}
else
{
lean_dec_ref(x_2);
return x_443;
}
}
default: 
{
lean_object* x_467; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_467 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_467, 0, x_2);
return x_467;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_12 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(x_4, x_5, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_135; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_135 = !lean_is_exclusive(x_13);
if (x_135 == 0)
{
x_16 = x_13;
x_17 = x_135;
goto block_134;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_18; lean_object* x_19; 
x_18 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1));
x_19 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_18, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = 1;
x_22 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5);
x_23 = 0;
x_24 = l_Lean_Compiler_LCNF_mkParam(x_21, x_20, x_22, x_23, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
lean_inc(x_28);
lean_inc(x_5);
lean_inc(x_26);
x_29 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(x_26, x_6, x_5, x_28, x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
x_32 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(x_30, x_31, x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_117; 
x_33 = lean_ctor_get(x_32, 0);
x_117 = !lean_is_exclusive(x_32);
if (x_117 == 0)
{
x_34 = x_32;
x_35 = x_117;
goto block_116;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_36; lean_object* x_37; 
x_36 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3));
x_37 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_36, x_8);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(x_27);
lean_inc(x_26);
x_40 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_23);
x_41 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4);
x_42 = lean_array_push(x_41, x_40);
x_43 = lean_array_push(x_42, x_25);
lean_inc_ref(x_1);
x_44 = l_Lean_Compiler_LCNF_mkFunDecl(x_21, x_38, x_1, x_43, x_33, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__6));
x_47 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_46, x_8);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc(x_5);
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 15);
lean_ctor_set(x_34, 0, x_5);
x_49 = x_34;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(x_91, 0, x_5);
x_49 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_50; 
x_50 = l_Lean_Compiler_LCNF_mkLetDecl(x_21, x_48, x_22, x_49, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_5);
x_54 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(x_5, x_15, x_52, x_53, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_56 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(x_5, x_15, x_52, x_53, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_15);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
lean_inc(x_53);
x_58 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(x_53, x_22, x_1, x_55, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_21, x_3, x_8);
lean_dec(x_8);
lean_dec_ref(x_3);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; uint8_t x_72; 
x_72 = !lean_is_exclusive(x_60);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_60, 0);
lean_dec(x_73);
x_61 = x_60;
x_62 = x_72;
goto block_71;
}
else
{
lean_dec(x_60);
x_61 = lean_box(0);
x_62 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_63; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_59);
lean_ctor_set(x_16, 0, x_51);
x_63 = x_16;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_59);
x_63 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_45);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Compiler_LCNF_attachCodeDecls(x_21, x_14, x_64);
lean_dec(x_14);
if (x_62 == 0)
{
lean_ctor_set(x_61, 0, x_65);
x_66 = x_61;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec(x_59);
lean_dec(x_51);
lean_dec(x_45);
lean_del_object(x_16);
lean_dec(x_14);
x_74 = lean_ctor_get(x_60, 0);
x_81 = !lean_is_exclusive(x_60);
if (x_81 == 0)
{
x_75 = x_60;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_60);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
else
{
lean_dec(x_51);
lean_dec(x_45);
lean_del_object(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_3);
return x_58;
}
}
else
{
lean_dec(x_55);
lean_dec(x_51);
lean_dec(x_45);
lean_del_object(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_56;
}
}
else
{
lean_dec(x_51);
lean_dec(x_45);
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_54;
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_dec(x_45);
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_82 = lean_ctor_get(x_50, 0);
x_89 = !lean_is_exclusive(x_50);
if (x_89 == 0)
{
x_83 = x_50;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_50);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_dec(x_45);
lean_del_object(x_34);
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_92 = lean_ctor_get(x_47, 0);
x_99 = !lean_is_exclusive(x_47);
if (x_99 == 0)
{
x_93 = x_47;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_47);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_107; 
lean_del_object(x_34);
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_100 = lean_ctor_get(x_44, 0);
x_107 = !lean_is_exclusive(x_44);
if (x_107 == 0)
{
x_101 = x_44;
x_102 = x_107;
goto block_106;
}
else
{
lean_inc(x_100);
lean_dec(x_44);
x_101 = lean_box(0);
x_102 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_103; 
if (x_102 == 0)
{
x_103 = x_101;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_100);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_115; 
lean_del_object(x_34);
lean_dec(x_33);
lean_dec(x_25);
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_108 = lean_ctor_get(x_37, 0);
x_115 = !lean_is_exclusive(x_37);
if (x_115 == 0)
{
x_109 = x_37;
x_110 = x_115;
goto block_114;
}
else
{
lean_inc(x_108);
lean_dec(x_37);
x_109 = lean_box(0);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_110 == 0)
{
x_111 = x_109;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_108);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
}
else
{
lean_dec(x_25);
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_32;
}
}
else
{
lean_dec(x_25);
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_29;
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_125; 
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_118 = lean_ctor_get(x_24, 0);
x_125 = !lean_is_exclusive(x_24);
if (x_125 == 0)
{
x_119 = x_24;
x_120 = x_125;
goto block_124;
}
else
{
lean_inc(x_118);
lean_dec(x_24);
x_119 = lean_box(0);
x_120 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_121; 
if (x_120 == 0)
{
x_121 = x_119;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_118);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_133; 
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_126 = lean_ctor_get(x_19, 0);
x_133 = !lean_is_exclusive(x_19);
if (x_133 == 0)
{
x_127 = x_19;
x_128 = x_133;
goto block_132;
}
else
{
lean_inc(x_126);
lean_dec(x_19);
x_127 = lean_box(0);
x_128 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_129; 
if (x_128 == 0)
{
x_129 = x_127;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_126);
x_129 = x_131;
goto block_130;
}
block_130:
{
return x_129;
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_143; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_136 = lean_ctor_get(x_12, 0);
x_143 = !lean_is_exclusive(x_12);
if (x_143 == 0)
{
x_137 = x_12;
x_138 = x_143;
goto block_142;
}
else
{
lean_inc(x_136);
lean_dec(x_12);
x_137 = lean_box(0);
x_138 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_139; 
if (x_138 == 0)
{
x_139 = x_137;
goto block_140;
}
else
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_136);
x_139 = x_141;
goto block_140;
}
block_140:
{
return x_139;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc_ref(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed), 7, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_array_fget_borrowed(x_3, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_13);
x_14 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(x_13, x_12, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ptr_addr(x_13);
x_17 = lean_ptr_addr(x_15);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = lean_array_fset(x_3, x_2, x_15);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
lean_dec(x_2);
x_2 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_14, 0);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
x_27 = x_14;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_22, 3);
if (lean_obj_tag(x_23) == 11)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_22);
x_24 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_24);
lean_dec_ref(x_1);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(x_3, x_2, x_22, x_25, x_26, x_24, x_4, x_5, x_6, x_7);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_28);
x_9 = x_1;
x_10 = x_2;
x_11 = x_28;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = lean_box(0);
goto block_21;
}
}
case 2:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_29, 2);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_29, 3);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_29, 4);
x_34 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_32);
lean_inc_ref(x_33);
x_35 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(x_33, x_34, x_32, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_56; 
x_36 = lean_ctor_get(x_35, 0);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
x_37 = x_35;
x_38 = x_56;
goto block_55;
}
else
{
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = x_56;
goto block_55;
}
block_55:
{
uint8_t x_39; lean_object* x_40; 
x_39 = 1;
x_40 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_39, x_29, x_32, x_31, x_36, x_5);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
if (x_38 == 0)
{
lean_ctor_set_tag(x_37, 2);
lean_ctor_set(x_37, 0, x_41);
x_42 = x_37;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_42 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_43; 
x_43 = lean_array_push(x_2, x_42);
x_1 = x_30;
x_2 = x_43;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_del_object(x_37);
lean_dec_ref(x_30);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_47 = lean_ctor_get(x_40, 0);
x_54 = !lean_is_exclusive(x_40);
if (x_54 == 0)
{
x_48 = x_40;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
else
{
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_35;
}
}
case 4:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_101; 
lean_dec_ref(x_3);
x_57 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_57, 0);
x_59 = lean_ctor_get(x_57, 1);
x_60 = lean_ctor_get(x_57, 2);
x_61 = lean_ctor_get(x_57, 3);
x_101 = !lean_is_exclusive(x_57);
if (x_101 == 0)
{
x_62 = x_57;
x_63 = x_101;
goto block_100;
}
else
{
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_57);
x_62 = lean_box(0);
x_63 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_61);
lean_inc_ref(x_59);
x_65 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(x_59, x_64, x_61, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_91; 
x_66 = lean_ctor_get(x_65, 0);
x_91 = !lean_is_exclusive(x_65);
if (x_91 == 0)
{
x_67 = x_65;
x_68 = x_91;
goto block_90;
}
else
{
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_box(0);
x_68 = x_91;
goto block_90;
}
block_90:
{
uint8_t x_69; lean_object* x_70; size_t x_76; size_t x_77; uint8_t x_78; 
x_69 = 1;
x_76 = lean_ptr_addr(x_61);
lean_dec_ref(x_61);
x_77 = lean_ptr_addr(x_66);
x_78 = lean_usize_dec_eq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; uint8_t x_88; 
x_88 = !lean_is_exclusive(x_1);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_1, 0);
lean_dec(x_89);
x_79 = x_1;
x_80 = x_88;
goto block_87;
}
else
{
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_81; 
if (x_63 == 0)
{
lean_ctor_set(x_62, 3, x_66);
x_81 = x_62;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_58);
lean_ctor_set(x_86, 1, x_59);
lean_ctor_set(x_86, 2, x_60);
lean_ctor_set(x_86, 3, x_66);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_80 == 0)
{
lean_ctor_set(x_79, 0, x_81);
x_82 = x_79;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_84, 0, x_81);
x_82 = x_84;
goto block_83;
}
block_83:
{
x_70 = x_82;
goto block_75;
}
}
}
}
else
{
lean_dec(x_66);
lean_del_object(x_62);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
x_70 = x_1;
goto block_75;
}
block_75:
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lean_Compiler_LCNF_attachCodeDecls(x_69, x_2, x_70);
lean_dec_ref(x_2);
if (x_68 == 0)
{
lean_ctor_set(x_67, 0, x_71);
x_72 = x_67;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_del_object(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_1);
lean_dec_ref(x_2);
x_92 = lean_ctor_get(x_65, 0);
x_99 = !lean_is_exclusive(x_65);
if (x_99 == 0)
{
x_93 = x_65;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_65);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
}
case 7:
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_102);
x_9 = x_1;
x_10 = x_2;
x_11 = x_102;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = lean_box(0);
goto block_21;
}
case 8:
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_103);
x_9 = x_1;
x_10 = x_2;
x_11 = x_103;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = lean_box(0);
goto block_21;
}
case 9:
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_104);
x_9 = x_1;
x_10 = x_2;
x_11 = x_104;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = lean_box(0);
goto block_21;
}
case 10:
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_105);
x_9 = x_1;
x_10 = x_2;
x_11 = x_105;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = lean_box(0);
goto block_21;
}
case 11:
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_106);
x_9 = x_1;
x_10 = x_2;
x_11 = x_106;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = lean_box(0);
goto block_21;
}
case 12:
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_107);
x_9 = x_1;
x_10 = x_2;
x_11 = x_107;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = lean_box(0);
goto block_21;
}
case 13:
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_108);
x_9 = x_1;
x_10 = x_2;
x_11 = x_108;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = lean_box(0);
goto block_21;
}
default: 
{
uint8_t x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_109 = 1;
x_110 = l_Lean_Compiler_LCNF_attachCodeDecls(x_109, x_2, x_1);
lean_dec_ref(x_2);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
block_21:
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 1;
x_18 = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(x_17, x_9);
lean_dec_ref(x_9);
x_19 = lean_array_push(x_10, x_18);
x_1 = x_11;
x_2 = x_19;
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
x_7 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0);
x_9 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(x_2, x_8, x_1, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_32; 
x_8 = lean_ctor_get(x_2, 0);
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
x_9 = x_2;
x_10 = x_32;
goto block_31;
}
else
{
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_11; 
x_11 = lean_apply_6(x_1, x_8, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
x_13 = x_11;
x_14 = x_22;
goto block_21;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_15; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_12);
x_15 = x_9;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_12);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
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
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_del_object(x_9);
x_23 = lean_ctor_get(x_11, 0);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
x_24 = x_11;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_2);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0);
x_10 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(x_2, x_9, x_8, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_getConfig___redArg(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_45; 
x_8 = lean_ctor_get(x_7, 0);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
x_9 = x_7;
x_10 = x_45;
goto block_44;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_45;
goto block_44;
}
block_44:
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*4 + 2);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_1);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_43; 
lean_del_object(x_9);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_18 = lean_ctor_get(x_1, 2);
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
x_19 = x_1;
x_20 = x_43;
goto block_42;
}
else
{
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_15);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed), 7, 1);
lean_closure_set(x_21, 0, x_15);
x_22 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(x_21, x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_33; 
x_23 = lean_ctor_get(x_22, 0);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
x_24 = x_22;
x_25 = x_33;
goto block_32;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_26; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_23);
x_26 = x_19;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_17);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_26);
x_27 = x_24;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_del_object(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
x_34 = lean_ctor_get(x_22, 0);
x_41 = !lean_is_exclusive(x_22);
if (x_41 == 0)
{
x_35 = x_22;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_7, 0);
x_53 = !lean_is_exclusive(x_7);
if (x_53 == 0)
{
x_47 = x_7;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_7);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__2));
x_3 = 2;
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__1));
x_5 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_expandResetReuse___closed__3, &l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2743268278u);
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
x_3 = 1;
x_4 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_expandResetReuse = _init_l_Lean_Compiler_LCNF_expandResetReuse();
lean_mark_persistent(l_Lean_Compiler_LCNF_expandResetReuse);
res = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PassManager(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
}
#ifdef __cplusplus
}
#endif
