// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Power
// Imports: import Init.Grind import Lean.Meta.Tactic.Grind.Arith.Simproc import Lean.Meta.NatInstTesters public import Lean.Meta.Tactic.Grind.PropagatorAttr
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__2_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__3_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "pow_add_congr"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__4_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value_aux_2),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(66, 167, 3, 17, 68, 5, 224, 21)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8_value;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_mkSemiringThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_196; 
x_18 = lean_st_ref_get(x_7);
x_19 = lean_ctor_get(x_6, 1);
x_196 = !lean_is_exclusive(x_6);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_6, 0);
lean_dec(x_197);
x_20 = x_6;
x_21 = x_196;
goto block_195;
}
else
{
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_22; 
lean_inc(x_19);
x_22 = l_Lean_Meta_Grind_Goal_getENode(x_18, x_19, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_25);
lean_dec(x_23);
lean_inc_ref(x_24);
x_26 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_24, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_178; 
x_27 = lean_ctor_get(x_26, 0);
x_178 = !lean_is_exclusive(x_26);
if (x_178 == 0)
{
x_28 = x_26;
x_29 = x_178;
goto block_177;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_30; lean_object* x_31; lean_object* x_45; lean_object* x_55; uint8_t x_56; 
x_30 = lean_box(0);
x_55 = l_Lean_Expr_cleanupAnnotations(x_27);
x_56 = l_Lean_Expr_isApp(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_55);
lean_dec_ref(x_24);
x_57 = lean_box(0);
x_58 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_57, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_45 = x_58;
goto block_54;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_59);
x_60 = l_Lean_Expr_appFnCleanup___redArg(x_55);
x_61 = l_Lean_Expr_isApp(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_24);
x_62 = lean_box(0);
x_63 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_62, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_45 = x_63;
goto block_54;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_64);
x_65 = l_Lean_Expr_appFnCleanup___redArg(x_60);
x_66 = l_Lean_Expr_isApp(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_24);
x_67 = lean_box(0);
x_68 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_67, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_45 = x_68;
goto block_54;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc_ref(x_69);
x_70 = l_Lean_Expr_appFnCleanup___redArg(x_65);
x_71 = l_Lean_Expr_isApp(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_24);
x_72 = lean_box(0);
x_73 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_72, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_45 = x_73;
goto block_54;
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_160; uint8_t x_161; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc_ref(x_74);
x_160 = l_Lean_Expr_appFnCleanup___redArg(x_70);
x_161 = l_Lean_Expr_isApp(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec_ref(x_160);
lean_dec_ref(x_74);
lean_dec_ref(x_69);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_24);
x_162 = lean_box(0);
x_163 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_162, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_45 = x_163;
goto block_54;
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_160, 1);
lean_inc_ref(x_164);
x_165 = l_Lean_Expr_appFnCleanup___redArg(x_160);
x_166 = l_Lean_Expr_isApp(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_165);
lean_dec_ref(x_164);
lean_dec_ref(x_74);
lean_dec_ref(x_69);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_24);
x_167 = lean_box(0);
x_168 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_167, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_45 = x_168;
goto block_54;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_169 = lean_ctor_get(x_165, 1);
lean_inc_ref(x_169);
x_170 = l_Lean_Expr_appFnCleanup___redArg(x_165);
x_171 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__8));
x_172 = l_Lean_Expr_isConstOf(x_170, x_171);
lean_dec_ref(x_170);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_169);
lean_dec_ref(x_164);
lean_dec_ref(x_74);
lean_dec_ref(x_69);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_24);
x_173 = lean_box(0);
x_174 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___lam__0(x_173, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_45 = x_174;
goto block_54;
}
else
{
uint8_t x_175; 
x_175 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_169);
lean_dec_ref(x_169);
if (x_175 == 0)
{
lean_dec_ref(x_164);
x_75 = x_175;
goto block_159;
}
else
{
uint8_t x_176; 
x_176 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_164);
lean_dec_ref(x_164);
x_75 = x_176;
goto block_159;
}
}
}
}
block_159:
{
if (x_75 == 0)
{
lean_dec_ref(x_74);
lean_dec_ref(x_69);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_24);
x_31 = lean_box(0);
goto block_44;
}
else
{
uint8_t x_76; 
x_76 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_2, x_74);
lean_dec_ref(x_74);
if (x_76 == 0)
{
lean_dec_ref(x_69);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_24);
x_31 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_77; 
x_77 = l_Lean_Meta_Structural_isInstHAddNat___redArg(x_69, x_14);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_24);
x_31 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = l_Lean_Expr_appFn_x21(x_3);
x_81 = l_Lean_Expr_appFn_x21(x_80);
lean_dec_ref(x_80);
lean_inc_ref(x_64);
lean_inc_ref(x_4);
lean_inc_ref(x_81);
x_82 = l_Lean_mkAppB(x_81, x_4, x_64);
lean_inc_ref(x_59);
lean_inc_ref(x_4);
x_83 = l_Lean_mkAppB(x_81, x_4, x_59);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_84 = l_Lean_Meta_mkMul(x_82, x_83, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_86 = lean_grind_preprocess(x_85, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = lean_ctor_get(x_87, 0);
lean_inc_ref(x_90);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_90);
x_91 = lean_grind_internalize(x_90, x_89, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_91);
x_92 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__5));
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_5);
x_93 = l_Lean_Meta_Grind_Arith_mkSemiringThm(x_92, x_5, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
if (lean_obj_tag(x_94) == 1)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_1);
x_96 = lean_grind_mk_eq_proof(x_1, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_98 = l_Lean_Meta_Simp_Result_getProof(x_87, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
lean_inc_ref(x_1);
lean_inc_ref(x_90);
lean_inc_ref(x_4);
x_100 = l_Lean_mkApp7(x_95, x_4, x_90, x_1, x_64, x_59, x_97, x_99);
x_101 = 0;
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_3);
x_102 = l_Lean_Meta_Grind_pushEqCore___redArg(x_3, x_90, x_100, x_101, x_7, x_9, x_13, x_14, x_15, x_16);
x_45 = x_102;
goto block_54;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec_ref(x_90);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_103 = lean_ctor_get(x_98, 0);
x_110 = !lean_is_exclusive(x_98);
if (x_110 == 0)
{
x_104 = x_98;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_box(0);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_105 == 0)
{
x_106 = x_104;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_103);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_dec(x_95);
lean_dec_ref(x_90);
lean_dec(x_87);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_96, 0);
x_118 = !lean_is_exclusive(x_96);
if (x_118 == 0)
{
x_112 = x_96;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_96);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
else
{
lean_dec(x_94);
lean_dec_ref(x_90);
lean_dec(x_87);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_24);
x_31 = lean_box(0);
goto block_44;
}
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_126; 
lean_dec_ref(x_90);
lean_dec(x_87);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_119 = lean_ctor_get(x_93, 0);
x_126 = !lean_is_exclusive(x_93);
if (x_126 == 0)
{
x_120 = x_93;
x_121 = x_126;
goto block_125;
}
else
{
lean_inc(x_119);
lean_dec(x_93);
x_120 = lean_box(0);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_121 == 0)
{
x_122 = x_120;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_119);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
}
else
{
lean_dec_ref(x_90);
lean_dec(x_87);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_24);
x_45 = x_91;
goto block_54;
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_134; 
lean_dec(x_87);
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_127 = lean_ctor_get(x_88, 0);
x_134 = !lean_is_exclusive(x_88);
if (x_134 == 0)
{
x_128 = x_88;
x_129 = x_134;
goto block_133;
}
else
{
lean_inc(x_127);
lean_dec(x_88);
x_128 = lean_box(0);
x_129 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_130; 
if (x_129 == 0)
{
x_130 = x_128;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_127);
x_130 = x_132;
goto block_131;
}
block_131:
{
return x_130;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_142; 
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_135 = lean_ctor_get(x_86, 0);
x_142 = !lean_is_exclusive(x_86);
if (x_142 == 0)
{
x_136 = x_86;
x_137 = x_142;
goto block_141;
}
else
{
lean_inc(x_135);
lean_dec(x_86);
x_136 = lean_box(0);
x_137 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_138; 
if (x_137 == 0)
{
x_138 = x_136;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_135);
x_138 = x_140;
goto block_139;
}
block_139:
{
return x_138;
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_150; 
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_143 = lean_ctor_get(x_84, 0);
x_150 = !lean_is_exclusive(x_84);
if (x_150 == 0)
{
x_144 = x_84;
x_145 = x_150;
goto block_149;
}
else
{
lean_inc(x_143);
lean_dec(x_84);
x_144 = lean_box(0);
x_145 = x_150;
goto block_149;
}
block_149:
{
lean_object* x_146; 
if (x_145 == 0)
{
x_146 = x_144;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_143);
x_146 = x_148;
goto block_147;
}
block_147:
{
return x_146;
}
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_158; 
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_151 = lean_ctor_get(x_77, 0);
x_158 = !lean_is_exclusive(x_77);
if (x_158 == 0)
{
x_152 = x_77;
x_153 = x_158;
goto block_157;
}
else
{
lean_inc(x_151);
lean_dec(x_77);
x_152 = lean_box(0);
x_153 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_154; 
if (x_153 == 0)
{
x_154 = x_152;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_151);
x_154 = x_156;
goto block_155;
}
block_155:
{
return x_154;
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
block_44:
{
uint8_t x_32; 
x_32 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_25, x_1);
if (x_32 == 0)
{
lean_object* x_33; 
lean_del_object(x_28);
lean_dec(x_19);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_30);
x_33 = x_20;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_25);
x_33 = x_36;
goto block_35;
}
block_35:
{
x_6 = x_33;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_25);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_37 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___closed__0));
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_37);
x_38 = x_20;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_19);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_38);
x_39 = x_28;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_38);
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
block_54:
{
if (lean_obj_tag(x_45) == 0)
{
lean_dec_ref(x_45);
x_31 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_del_object(x_28);
lean_dec_ref(x_25);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_45, 0);
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
x_47 = x_45;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_45);
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
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_186; 
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_179 = lean_ctor_get(x_26, 0);
x_186 = !lean_is_exclusive(x_26);
if (x_186 == 0)
{
x_180 = x_26;
x_181 = x_186;
goto block_185;
}
else
{
lean_inc(x_179);
lean_dec(x_26);
x_180 = lean_box(0);
x_181 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_182; 
if (x_181 == 0)
{
x_182 = x_180;
goto block_183;
}
else
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_179);
x_182 = x_184;
goto block_183;
}
block_183:
{
return x_182;
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_194; 
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_187 = lean_ctor_get(x_22, 0);
x_194 = !lean_is_exclusive(x_22);
if (x_194 == 0)
{
x_188 = x_22;
x_189 = x_194;
goto block_193;
}
else
{
lean_inc(x_187);
lean_dec(x_22);
x_188 = lean_box(0);
x_189 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_190; 
if (x_189 == 0)
{
x_190 = x_188;
goto block_191;
}
else
{
lean_object* x_192; 
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_187);
x_190 = x_192;
goto block_191;
}
block_191:
{
return x_190;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_33);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_35 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
x_36 = l_Lean_Expr_isConstOf(x_34, x_35);
lean_dec_ref(x_34);
if (x_36 == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_inc_ref(x_30);
x_37 = l_Lean_Expr_cleanupAnnotations(x_30);
x_38 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4));
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
lean_dec_ref(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_33, x_27);
lean_dec_ref(x_27);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_box(0);
lean_inc_ref(x_19);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_19);
x_47 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(x_19, x_30, x_1, x_22, x_33, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_30);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_61; 
x_48 = lean_ctor_get(x_47, 0);
x_61 = !lean_is_exclusive(x_47);
if (x_61 == 0)
{
x_49 = x_47;
x_50 = x_61;
goto block_60;
}
else
{
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
if (x_50 == 0)
{
lean_ctor_set(x_49, 0, x_52);
x_53 = x_49;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
lean_dec_ref(x_51);
if (x_50 == 0)
{
lean_ctor_set(x_49, 0, x_56);
x_57 = x_49;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
x_62 = lean_ctor_get(x_47, 0);
x_69 = !lean_is_exclusive(x_47);
if (x_69 == 0)
{
x_63 = x_47;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_47);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
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
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_propagatePower(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
return x_2;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
}
#ifdef __cplusplus
}
#endif
