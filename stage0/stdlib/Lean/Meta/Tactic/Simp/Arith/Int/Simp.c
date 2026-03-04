// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Simp
// Imports: public import Lean.Meta.Tactic.Simp.Arith.Util public import Lean.Meta.Tactic.Simp.Arith.Int.Basic
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "norm_eq_var_const"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(35, 112, 223, 250, 183, 82, 157, 139)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_eq_false_of_divCoeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(155, 236, 46, 169, 167, 124, 63, 211)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
lean_object* l_Lean_mkIntLit(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "norm_eq_coeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(85, 43, 120, 188, 118, 245, 143, 91)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(44, 156, 243, 152, 103, 234, 174, 123)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
lean_object* lean_int_neg(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "norm_eq_var"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value),LEAN_SCALAR_PTR_LITERAL(135, 64, 142, 174, 60, 214, 97, 115)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_eq_true"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value),LEAN_SCALAR_PTR_LITERAL(22, 67, 32, 138, 58, 105, 16, 18)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eq_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value),LEAN_SCALAR_PTR_LITERAL(235, 105, 48, 217, 98, 238, 131, 5)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44;
lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object*);
uint8_t l_Int_Linear_Poly_isValidEq(lean_object*);
lean_object* l_Int_Linear_Poly_toExpr(lean_object*);
uint8_t l_Int_Linear_instBEqExpr_beq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "norm_le_coeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 68, 185, 68, 63, 172, 180, 150)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "norm_le_coeff_tight"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 199, 217, 219, 136, 132, 30, 204)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(232, 121, 64, 164, 96, 91, 136, 25)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "le_eq_true"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(168, 245, 170, 32, 204, 84, 255, 159)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "le_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(76, 250, 170, 64, 206, 9, 106, 135)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value;
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
uint8_t l_Int_Linear_Poly_isValidLe(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value;
extern lean_object* l_Lean_levelOne;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
lean_object* l_Lean_mkSort(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_le_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(77, 74, 162, 108, 148, 71, 165, 71)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_ge_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(87, 141, 152, 40, 61, 44, 151, 4)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_lt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(214, 41, 233, 126, 147, 68, 29, 47)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_gt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(250, 161, 48, 12, 204, 229, 102, 4)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "norm_dvd_gcd"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 243, 25, 22, 225, 48, 108, 155)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "norm_dvd"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(14, 102, 31, 143, 124, 229, 161, 52)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dvd_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 255, 101, 122, 145, 117, 61, 183)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "eq_of_norm_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 62, 222, 142, 91, 249, 126, 146)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(53, 220, 199, 2, 108, 141, 83, 34)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_nat_abs(x_5);
x_7 = lean_nat_gcd(x_1, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_nat_abs(x_8);
x_11 = lean_nat_gcd(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_9;
goto _start;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_nat_abs(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_abs(x_4);
x_7 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_gcdAll(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_abs(x_5);
x_8 = lean_nat_gcd(x_1, x_7);
lean_dec(x_7);
lean_dec(x_1);
x_1 = x_8;
x_2 = x_6;
goto _start;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(1u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_abs(x_3);
x_6 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(x_5, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_gcdCoeffs_x27(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_get_borrowed(x_1, x_2, x_3);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_383; 
x_8 = lean_ctor_get(x_7, 0);
x_383 = !lean_is_exclusive(x_7);
if (x_383 == 0)
{
x_9 = x_7;
x_10 = x_383;
goto block_382;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_383;
goto block_382;
}
block_382:
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_377; 
x_11 = lean_ctor_get(x_8, 0);
x_377 = !lean_is_exclusive(x_8);
if (x_377 == 0)
{
x_12 = x_8;
x_13 = x_377;
goto block_376;
}
else
{
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = x_377;
goto block_376;
}
block_376:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_375; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_11, 0);
x_375 = !lean_is_exclusive(x_11);
if (x_375 == 0)
{
x_16 = x_11;
x_17 = x_375;
goto block_374;
}
else
{
lean_inc(x_14);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_375;
goto block_374;
}
block_374:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_373; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
x_373 = !lean_is_exclusive(x_14);
if (x_373 == 0)
{
x_20 = x_14;
x_21 = x_373;
goto block_372;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = x_373;
goto block_372;
}
block_372:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_instInhabitedExpr;
lean_inc(x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_19);
lean_inc(x_15);
lean_inc_ref(x_23);
x_24 = l_Int_Linear_Expr_denoteExpr___redArg(x_23, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_363; 
x_25 = lean_ctor_get(x_24, 0);
x_363 = !lean_is_exclusive(x_24);
if (x_363 == 0)
{
x_26 = x_24;
x_27 = x_363;
goto block_362;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_363;
goto block_362;
}
block_362:
{
lean_object* x_28; 
lean_inc(x_18);
lean_inc_ref(x_23);
x_28 = l_Int_Linear_Expr_denoteExpr___redArg(x_23, x_18);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_353; 
x_29 = lean_ctor_get(x_28, 0);
x_353 = !lean_is_exclusive(x_28);
if (x_353 == 0)
{
x_30 = x_28;
x_31 = x_353;
goto block_352;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_353;
goto block_352;
}
block_352:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_222; uint8_t x_292; 
x_32 = l_Lean_mkIntEq(x_25, x_29);
lean_inc(x_18);
lean_inc(x_15);
x_106 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_106, 0, x_15);
lean_ctor_set(x_106, 1, x_18);
x_107 = l_Int_Linear_Expr_norm(x_106);
lean_dec_ref(x_106);
x_292 = l_Int_Linear_Poly_isUnsatEq(x_107);
if (x_292 == 0)
{
uint8_t x_293; 
x_293 = l_Int_Linear_Poly_isValidEq(x_107);
if (x_293 == 0)
{
lean_object* x_294; uint8_t x_295; 
lean_inc_ref(x_107);
x_294 = l_Int_Linear_Poly_toExpr(x_107);
x_295 = l_Int_Linear_instBEqExpr_beq(x_294, x_15);
lean_dec_ref(x_294);
if (x_295 == 0)
{
x_222 = x_295;
goto block_291;
}
else
{
lean_object* x_296; uint8_t x_297; 
x_296 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35);
x_297 = l_Int_Linear_instBEqExpr_beq(x_18, x_296);
x_222 = x_297;
goto block_291;
}
}
else
{
lean_object* x_298; 
lean_dec_ref(x_107);
lean_del_object(x_30);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_del_object(x_16);
lean_del_object(x_12);
lean_del_object(x_9);
x_298 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; uint8_t x_316; 
x_299 = lean_ctor_get(x_298, 0);
x_316 = !lean_is_exclusive(x_298);
if (x_316 == 0)
{
x_300 = x_298;
x_301 = x_316;
goto block_315;
}
else
{
lean_inc(x_299);
lean_dec(x_298);
x_300 = lean_box(0);
x_301 = x_316;
goto block_315;
}
block_315:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_302 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38);
x_303 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41);
x_304 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_305 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_306 = l_Lean_eagerReflBoolTrue;
x_307 = l_Lean_mkApp4(x_303, x_299, x_304, x_305, x_306);
x_308 = l_Lean_mkPropEq(x_32, x_302);
x_309 = l_Lean_Meta_mkExpectedPropHint(x_307, x_308);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_302);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_310);
if (x_301 == 0)
{
lean_ctor_set(x_300, 0, x_311);
x_312 = x_300;
goto block_313;
}
else
{
lean_object* x_314; 
x_314 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_314, 0, x_311);
x_312 = x_314;
goto block_313;
}
block_313:
{
return x_312;
}
}
}
else
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; uint8_t x_324; 
lean_dec_ref(x_32);
lean_dec(x_18);
lean_dec(x_15);
x_317 = lean_ctor_get(x_298, 0);
x_324 = !lean_is_exclusive(x_298);
if (x_324 == 0)
{
x_318 = x_298;
x_319 = x_324;
goto block_323;
}
else
{
lean_inc(x_317);
lean_dec(x_298);
x_318 = lean_box(0);
x_319 = x_324;
goto block_323;
}
block_323:
{
lean_object* x_320; 
if (x_319 == 0)
{
x_320 = x_318;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_317);
x_320 = x_322;
goto block_321;
}
block_321:
{
return x_320;
}
}
}
}
}
else
{
lean_object* x_325; 
lean_dec_ref(x_107);
lean_del_object(x_30);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_del_object(x_16);
lean_del_object(x_12);
lean_del_object(x_9);
x_325 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; uint8_t x_328; uint8_t x_343; 
x_326 = lean_ctor_get(x_325, 0);
x_343 = !lean_is_exclusive(x_325);
if (x_343 == 0)
{
x_327 = x_325;
x_328 = x_343;
goto block_342;
}
else
{
lean_inc(x_326);
lean_dec(x_325);
x_327 = lean_box(0);
x_328 = x_343;
goto block_342;
}
block_342:
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_329 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
x_330 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44);
x_331 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_332 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_333 = l_Lean_eagerReflBoolTrue;
x_334 = l_Lean_mkApp4(x_330, x_326, x_331, x_332, x_333);
x_335 = l_Lean_mkPropEq(x_32, x_329);
x_336 = l_Lean_Meta_mkExpectedPropHint(x_334, x_335);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_329);
lean_ctor_set(x_337, 1, x_336);
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_337);
if (x_328 == 0)
{
lean_ctor_set(x_327, 0, x_338);
x_339 = x_327;
goto block_340;
}
else
{
lean_object* x_341; 
x_341 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_341, 0, x_338);
x_339 = x_341;
goto block_340;
}
block_340:
{
return x_339;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; uint8_t x_346; uint8_t x_351; 
lean_dec_ref(x_32);
lean_dec(x_18);
lean_dec(x_15);
x_344 = lean_ctor_get(x_325, 0);
x_351 = !lean_is_exclusive(x_325);
if (x_351 == 0)
{
x_345 = x_325;
x_346 = x_351;
goto block_350;
}
else
{
lean_inc(x_344);
lean_dec(x_325);
x_345 = lean_box(0);
x_346 = x_351;
goto block_350;
}
block_350:
{
lean_object* x_347; 
if (x_346 == 0)
{
x_347 = x_345;
goto block_348;
}
else
{
lean_object* x_349; 
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_344);
x_347 = x_349;
goto block_348;
}
block_348:
{
return x_347;
}
}
}
}
block_53:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_Lean_eagerReflBoolTrue;
x_41 = l_Lean_mkApp5(x_38, x_35, x_36, x_34, x_39, x_40);
lean_inc_ref(x_33);
x_42 = l_Lean_mkPropEq(x_32, x_33);
x_43 = l_Lean_Meta_mkExpectedPropHint(x_41, x_42);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_43);
lean_ctor_set(x_20, 0, x_33);
x_44 = x_20;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_43);
x_44 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_45; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_44);
x_45 = x_12;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_44);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_45);
x_46 = x_30;
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
}
block_73:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = l_Lean_eagerReflBoolTrue;
x_63 = l_Lean_mkApp6(x_55, x_59, x_57, x_58, x_60, x_61, x_62);
lean_inc_ref(x_54);
x_64 = l_Lean_mkPropEq(x_32, x_54);
x_65 = l_Lean_Meta_mkExpectedPropHint(x_63, x_64);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_65);
lean_ctor_set(x_16, 0, x_54);
x_66 = x_16;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_54);
lean_ctor_set(x_72, 1, x_65);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_67);
x_68 = x_26;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
block_105:
{
lean_object* x_77; 
x_77 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_96; 
x_78 = lean_ctor_get(x_77, 0);
x_96 = !lean_is_exclusive(x_77);
if (x_96 == 0)
{
x_79 = x_77;
x_80 = x_96;
goto block_95;
}
else
{
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_box(0);
x_80 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_inc_ref(x_76);
x_81 = l_Lean_mkIntEq(x_74, x_76);
x_82 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4);
x_83 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_84 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_85 = l_Lean_mkNatLit(x_75);
x_86 = l_Lean_eagerReflBoolTrue;
x_87 = l_Lean_mkApp6(x_82, x_78, x_83, x_84, x_85, x_76, x_86);
lean_inc_ref(x_81);
x_88 = l_Lean_mkPropEq(x_32, x_81);
x_89 = l_Lean_Meta_mkExpectedPropHint(x_87, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_81);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
if (x_80 == 0)
{
lean_ctor_set(x_79, 0, x_91);
x_92 = x_79;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_91);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_104; 
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_32);
lean_dec(x_18);
lean_dec(x_15);
x_97 = lean_ctor_get(x_77, 0);
x_104 = !lean_is_exclusive(x_77);
if (x_104 == 0)
{
x_98 = x_77;
x_99 = x_104;
goto block_103;
}
else
{
lean_inc(x_97);
lean_dec(x_77);
x_98 = lean_box(0);
x_99 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_100; 
if (x_99 == 0)
{
x_100 = x_98;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_97);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
}
}
}
}
block_221:
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = l_Int_Linear_Poly_gcdCoeffs_x27(x_107);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_dec_eq(x_113, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = l_Int_Linear_Poly_getConst(x_107);
x_117 = lean_nat_to_int(x_113);
x_118 = lean_int_emod(x_116, x_117);
lean_dec(x_116);
x_119 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_120 = lean_int_dec_eq(x_118, x_119);
lean_dec(x_118);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec_ref(x_107);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_16);
x_121 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_108, x_109, x_110, x_111);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
x_124 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11);
x_125 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_126 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_127 = lean_int_dec_le(x_119, x_117);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_129 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_130 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_131 = lean_int_neg(x_117);
lean_dec(x_117);
x_132 = l_Int_toNat(x_131);
lean_dec(x_131);
x_133 = l_Lean_instToExprInt_mkNat(x_132);
x_134 = l_Lean_mkApp3(x_128, x_129, x_130, x_133);
x_33 = x_123;
x_34 = x_126;
x_35 = x_122;
x_36 = x_125;
x_37 = lean_box(0);
x_38 = x_124;
x_39 = x_134;
goto block_53;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = l_Int_toNat(x_117);
lean_dec(x_117);
x_136 = l_Lean_instToExprInt_mkNat(x_135);
x_33 = x_123;
x_34 = x_126;
x_35 = x_122;
x_36 = x_125;
x_37 = lean_box(0);
x_38 = x_124;
x_39 = x_136;
goto block_53;
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_144; 
lean_dec(x_117);
lean_dec_ref(x_32);
lean_del_object(x_30);
lean_del_object(x_20);
lean_dec(x_18);
lean_dec(x_15);
lean_del_object(x_12);
x_137 = lean_ctor_get(x_121, 0);
x_144 = !lean_is_exclusive(x_121);
if (x_144 == 0)
{
x_138 = x_121;
x_139 = x_144;
goto block_143;
}
else
{
lean_inc(x_137);
lean_dec(x_121);
x_138 = lean_box(0);
x_139 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_140; 
if (x_139 == 0)
{
x_140 = x_138;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_137);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_del_object(x_30);
lean_del_object(x_20);
lean_del_object(x_12);
x_145 = l_Int_Linear_Poly_div(x_117, x_107);
lean_inc_ref(x_145);
x_146 = l_Int_Linear_Poly_denoteExpr___redArg(x_23, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_108, x_109, x_110, x_111);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
x_151 = l_Lean_mkIntEq(x_147, x_150);
x_152 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26);
x_153 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_154 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_155 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_145);
x_156 = lean_int_dec_le(x_119, x_117);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_157 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_158 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_159 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_160 = lean_int_neg(x_117);
lean_dec(x_117);
x_161 = l_Int_toNat(x_160);
lean_dec(x_160);
x_162 = l_Lean_instToExprInt_mkNat(x_161);
x_163 = l_Lean_mkApp3(x_157, x_158, x_159, x_162);
x_54 = x_151;
x_55 = x_152;
x_56 = lean_box(0);
x_57 = x_153;
x_58 = x_154;
x_59 = x_149;
x_60 = x_155;
x_61 = x_163;
goto block_73;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Int_toNat(x_117);
lean_dec(x_117);
x_165 = l_Lean_instToExprInt_mkNat(x_164);
x_54 = x_151;
x_55 = x_152;
x_56 = lean_box(0);
x_57 = x_153;
x_58 = x_154;
x_59 = x_149;
x_60 = x_155;
x_61 = x_165;
goto block_73;
}
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_173; 
lean_dec(x_147);
lean_dec_ref(x_145);
lean_dec(x_117);
lean_dec_ref(x_32);
lean_del_object(x_26);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
x_166 = lean_ctor_get(x_148, 0);
x_173 = !lean_is_exclusive(x_148);
if (x_173 == 0)
{
x_167 = x_148;
x_168 = x_173;
goto block_172;
}
else
{
lean_inc(x_166);
lean_dec(x_148);
x_167 = lean_box(0);
x_168 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_169; 
if (x_168 == 0)
{
x_169 = x_167;
goto block_170;
}
else
{
lean_object* x_171; 
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_166);
x_169 = x_171;
goto block_170;
}
block_170:
{
return x_169;
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_181; 
lean_dec_ref(x_145);
lean_dec(x_117);
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_32);
lean_del_object(x_26);
lean_dec(x_19);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
x_174 = lean_ctor_get(x_146, 0);
x_181 = !lean_is_exclusive(x_146);
if (x_181 == 0)
{
x_175 = x_146;
x_176 = x_181;
goto block_180;
}
else
{
lean_inc(x_174);
lean_dec(x_146);
x_175 = lean_box(0);
x_176 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_177; 
if (x_176 == 0)
{
x_177 = x_175;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_174);
x_177 = x_179;
goto block_178;
}
block_178:
{
return x_177;
}
}
}
}
}
else
{
lean_object* x_182; 
lean_dec(x_113);
lean_del_object(x_30);
lean_del_object(x_26);
lean_del_object(x_20);
lean_del_object(x_16);
lean_del_object(x_12);
lean_inc_ref(x_107);
x_182 = l_Int_Linear_Poly_denoteExpr___redArg(x_23, x_107);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_108, x_109, x_110, x_111);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_204; 
x_185 = lean_ctor_get(x_184, 0);
x_204 = !lean_is_exclusive(x_184);
if (x_204 == 0)
{
x_186 = x_184;
x_187 = x_204;
goto block_203;
}
else
{
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_box(0);
x_187 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_188 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
x_189 = l_Lean_mkIntEq(x_183, x_188);
x_190 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29);
x_191 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_192 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_193 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_107);
x_194 = l_Lean_eagerReflBoolTrue;
x_195 = l_Lean_mkApp5(x_190, x_185, x_191, x_192, x_193, x_194);
lean_inc_ref(x_189);
x_196 = l_Lean_mkPropEq(x_32, x_189);
x_197 = l_Lean_Meta_mkExpectedPropHint(x_195, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
if (x_187 == 0)
{
lean_ctor_set(x_186, 0, x_199);
x_200 = x_186;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_199);
x_200 = x_202;
goto block_201;
}
block_201:
{
return x_200;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; uint8_t x_212; 
lean_dec(x_183);
lean_dec_ref(x_107);
lean_dec_ref(x_32);
lean_dec(x_18);
lean_dec(x_15);
x_205 = lean_ctor_get(x_184, 0);
x_212 = !lean_is_exclusive(x_184);
if (x_212 == 0)
{
x_206 = x_184;
x_207 = x_212;
goto block_211;
}
else
{
lean_inc(x_205);
lean_dec(x_184);
x_206 = lean_box(0);
x_207 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_208; 
if (x_207 == 0)
{
x_208 = x_206;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_205);
x_208 = x_210;
goto block_209;
}
block_209:
{
return x_208;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_220; 
lean_dec(x_111);
lean_dec_ref(x_110);
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_32);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
x_213 = lean_ctor_get(x_182, 0);
x_220 = !lean_is_exclusive(x_182);
if (x_220 == 0)
{
x_214 = x_182;
x_215 = x_220;
goto block_219;
}
else
{
lean_inc(x_213);
lean_dec(x_182);
x_214 = lean_box(0);
x_215 = x_220;
goto block_219;
}
block_219:
{
lean_object* x_216; 
if (x_215 == 0)
{
x_216 = x_214;
goto block_217;
}
else
{
lean_object* x_218; 
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_213);
x_216 = x_218;
goto block_217;
}
block_217:
{
return x_216;
}
}
}
}
}
block_291:
{
if (x_222 == 0)
{
lean_del_object(x_9);
if (lean_obj_tag(x_107) == 1)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_223 = lean_ctor_get(x_107, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_107, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_107, 2);
lean_inc_ref(x_225);
x_226 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
x_227 = lean_int_dec_eq(x_223, x_226);
lean_dec(x_223);
if (x_227 == 0)
{
lean_dec_ref(x_225);
lean_dec(x_224);
x_108 = x_2;
x_109 = x_3;
x_110 = x_4;
x_111 = x_5;
x_112 = lean_box(0);
goto block_221;
}
else
{
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
lean_dec_ref(x_107);
lean_del_object(x_30);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_del_object(x_16);
lean_del_object(x_12);
x_228 = lean_ctor_get(x_225, 0);
lean_inc(x_228);
lean_dec_ref(x_225);
x_229 = lean_array_get_borrowed(x_22, x_19, x_224);
x_230 = lean_int_neg(x_228);
lean_dec(x_228);
x_231 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_232 = lean_int_dec_le(x_231, x_230);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_233 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_234 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_235 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_236 = lean_int_neg(x_230);
lean_dec(x_230);
x_237 = l_Int_toNat(x_236);
lean_dec(x_236);
x_238 = l_Lean_instToExprInt_mkNat(x_237);
x_239 = l_Lean_mkApp3(x_233, x_234, x_235, x_238);
lean_inc(x_229);
x_74 = x_229;
x_75 = x_224;
x_76 = x_239;
goto block_105;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = l_Int_toNat(x_230);
lean_dec(x_230);
x_241 = l_Lean_instToExprInt_mkNat(x_240);
lean_inc(x_229);
x_74 = x_229;
x_75 = x_224;
x_76 = x_241;
goto block_105;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_242 = lean_ctor_get(x_225, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_225, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_225, 2);
lean_inc_ref(x_244);
lean_dec_ref(x_225);
x_245 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
x_246 = lean_int_dec_eq(x_242, x_245);
lean_dec(x_242);
if (x_246 == 0)
{
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec(x_224);
x_108 = x_2;
x_109 = x_3;
x_110 = x_4;
x_111 = x_5;
x_112 = lean_box(0);
goto block_221;
}
else
{
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; uint8_t x_286; 
x_247 = lean_ctor_get(x_244, 0);
x_286 = !lean_is_exclusive(x_244);
if (x_286 == 0)
{
x_248 = x_244;
x_249 = x_286;
goto block_285;
}
else
{
lean_inc(x_247);
lean_dec(x_244);
x_248 = lean_box(0);
x_249 = x_286;
goto block_285;
}
block_285:
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_251 = lean_int_dec_eq(x_247, x_250);
lean_dec(x_247);
if (x_251 == 0)
{
lean_del_object(x_248);
lean_dec(x_243);
lean_dec(x_224);
x_108 = x_2;
x_109 = x_3;
x_110 = x_4;
x_111 = x_5;
x_112 = lean_box(0);
goto block_221;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec_ref(x_107);
lean_del_object(x_30);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_del_object(x_16);
lean_del_object(x_12);
x_252 = lean_array_get(x_22, x_19, x_224);
x_253 = lean_array_get(x_22, x_19, x_243);
x_254 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_276; 
x_255 = lean_ctor_get(x_254, 0);
x_276 = !lean_is_exclusive(x_254);
if (x_276 == 0)
{
x_256 = x_254;
x_257 = x_276;
goto block_275;
}
else
{
lean_inc(x_255);
lean_dec(x_254);
x_256 = lean_box(0);
x_257 = x_276;
goto block_275;
}
block_275:
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_258 = l_Lean_mkIntEq(x_252, x_253);
x_259 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34);
x_260 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_261 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_18);
x_262 = l_Lean_mkNatLit(x_224);
x_263 = l_Lean_mkNatLit(x_243);
x_264 = l_Lean_eagerReflBoolTrue;
x_265 = l_Lean_mkApp6(x_259, x_255, x_260, x_261, x_262, x_263, x_264);
lean_inc_ref(x_258);
x_266 = l_Lean_mkPropEq(x_32, x_258);
x_267 = l_Lean_Meta_mkExpectedPropHint(x_265, x_266);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_258);
lean_ctor_set(x_268, 1, x_267);
if (x_249 == 0)
{
lean_ctor_set_tag(x_248, 1);
lean_ctor_set(x_248, 0, x_268);
x_269 = x_248;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_268);
x_269 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_270; 
if (x_257 == 0)
{
lean_ctor_set(x_256, 0, x_269);
x_270 = x_256;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_269);
x_270 = x_272;
goto block_271;
}
block_271:
{
return x_270;
}
}
}
}
else
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; uint8_t x_284; 
lean_dec(x_253);
lean_dec(x_252);
lean_del_object(x_248);
lean_dec(x_243);
lean_dec(x_224);
lean_dec_ref(x_32);
lean_dec(x_18);
lean_dec(x_15);
x_277 = lean_ctor_get(x_254, 0);
x_284 = !lean_is_exclusive(x_254);
if (x_284 == 0)
{
x_278 = x_254;
x_279 = x_284;
goto block_283;
}
else
{
lean_inc(x_277);
lean_dec(x_254);
x_278 = lean_box(0);
x_279 = x_284;
goto block_283;
}
block_283:
{
lean_object* x_280; 
if (x_279 == 0)
{
x_280 = x_278;
goto block_281;
}
else
{
lean_object* x_282; 
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_277);
x_280 = x_282;
goto block_281;
}
block_281:
{
return x_280;
}
}
}
}
}
}
else
{
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec(x_224);
x_108 = x_2;
x_109 = x_3;
x_110 = x_4;
x_111 = x_5;
x_112 = lean_box(0);
goto block_221;
}
}
}
}
}
else
{
x_108 = x_2;
x_109 = x_3;
x_110 = x_4;
x_111 = x_5;
x_112 = lean_box(0);
goto block_221;
}
}
else
{
lean_object* x_287; lean_object* x_288; 
lean_dec_ref(x_107);
lean_dec_ref(x_32);
lean_del_object(x_30);
lean_del_object(x_26);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
lean_del_object(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_287 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_287);
x_288 = x_9;
goto block_289;
}
else
{
lean_object* x_290; 
x_290 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_290, 0, x_287);
x_288 = x_290;
goto block_289;
}
block_289:
{
return x_288;
}
}
}
}
}
else
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; uint8_t x_361; 
lean_del_object(x_26);
lean_dec(x_25);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
lean_del_object(x_12);
lean_del_object(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_354 = lean_ctor_get(x_28, 0);
x_361 = !lean_is_exclusive(x_28);
if (x_361 == 0)
{
x_355 = x_28;
x_356 = x_361;
goto block_360;
}
else
{
lean_inc(x_354);
lean_dec(x_28);
x_355 = lean_box(0);
x_356 = x_361;
goto block_360;
}
block_360:
{
lean_object* x_357; 
if (x_356 == 0)
{
x_357 = x_355;
goto block_358;
}
else
{
lean_object* x_359; 
x_359 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_359, 0, x_354);
x_357 = x_359;
goto block_358;
}
block_358:
{
return x_357;
}
}
}
}
}
else
{
lean_object* x_364; lean_object* x_365; uint8_t x_366; uint8_t x_371; 
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
lean_del_object(x_12);
lean_del_object(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_364 = lean_ctor_get(x_24, 0);
x_371 = !lean_is_exclusive(x_24);
if (x_371 == 0)
{
x_365 = x_24;
x_366 = x_371;
goto block_370;
}
else
{
lean_inc(x_364);
lean_dec(x_24);
x_365 = lean_box(0);
x_366 = x_371;
goto block_370;
}
block_370:
{
lean_object* x_367; 
if (x_366 == 0)
{
x_367 = x_365;
goto block_368;
}
else
{
lean_object* x_369; 
x_369 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_369, 0, x_364);
x_367 = x_369;
goto block_368;
}
block_368:
{
return x_367;
}
}
}
}
}
}
}
else
{
lean_object* x_378; lean_object* x_379; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_378 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_378);
x_379 = x_9;
goto block_380;
}
else
{
lean_object* x_381; 
x_381 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_381, 0, x_378);
x_379 = x_381;
goto block_380;
}
block_380:
{
return x_379;
}
}
}
}
else
{
lean_object* x_384; lean_object* x_385; uint8_t x_386; uint8_t x_391; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_384 = lean_ctor_get(x_7, 0);
x_391 = !lean_is_exclusive(x_7);
if (x_391 == 0)
{
x_385 = x_7;
x_386 = x_391;
goto block_390;
}
else
{
lean_inc(x_384);
lean_dec(x_7);
x_385 = lean_box(0);
x_386 = x_391;
goto block_390;
}
block_390:
{
lean_object* x_387; 
if (x_386 == 0)
{
x_387 = x_385;
goto block_388;
}
else
{
lean_object* x_389; 
x_389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_389, 0, x_384);
x_387 = x_389;
goto block_388;
}
block_388:
{
return x_387;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_180; uint8_t x_181; lean_object* x_320; uint8_t x_321; 
x_180 = l_Lean_instInhabitedExpr;
x_320 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
x_321 = l_Lean_Expr_isAppOf(x_1, x_320);
if (x_321 == 0)
{
x_181 = x_321;
goto block_319;
}
else
{
x_181 = x_2;
goto block_319;
}
block_17:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc_ref(x_9);
x_12 = l_Lean_mkPropEq(x_8, x_9);
x_13 = l_Lean_Meta_mkExpectedPropHint(x_10, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_eagerReflBoolTrue;
x_28 = l_Lean_mkApp6(x_20, x_19, x_23, x_22, x_21, x_26, x_27);
x_8 = x_18;
x_9 = x_24;
x_10 = x_28;
x_11 = lean_box(0);
goto block_17;
}
block_41:
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_eagerReflBoolTrue;
x_40 = l_Lean_mkApp6(x_33, x_36, x_32, x_34, x_30, x_38, x_39);
x_8 = x_31;
x_9 = x_37;
x_10 = x_40;
x_11 = lean_box(0);
goto block_17;
}
block_122:
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Int_Linear_Poly_div(x_47, x_46);
lean_inc_ref(x_53);
x_54 = l_Int_Linear_Poly_denoteExpr___redArg(x_45, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = l_Lean_mkIntLit(x_42);
x_57 = l_Lean_mkIntLE(x_55, x_56);
if (x_52 == 0)
{
lean_object* x_58; 
x_58 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_43, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_box(0);
x_61 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2);
x_62 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_50);
x_63 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_49);
x_64 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_53);
x_65 = lean_int_dec_le(x_42, x_47);
lean_dec(x_42);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14));
x_67 = l_Lean_Level_ofNat(x_48);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_60);
x_69 = l_Lean_Expr_const___override(x_66, x_68);
x_70 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_71 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_72 = lean_int_neg(x_47);
lean_dec(x_47);
x_73 = l_Int_toNat(x_72);
lean_dec(x_72);
x_74 = l_Lean_instToExprInt_mkNat(x_73);
x_75 = l_Lean_mkApp3(x_69, x_70, x_71, x_74);
x_30 = x_64;
x_31 = x_44;
x_32 = x_62;
x_33 = x_61;
x_34 = x_63;
x_35 = lean_box(0);
x_36 = x_59;
x_37 = x_57;
x_38 = x_75;
goto block_41;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Int_toNat(x_47);
lean_dec(x_47);
x_77 = l_Lean_instToExprInt_mkNat(x_76);
x_30 = x_64;
x_31 = x_44;
x_32 = x_62;
x_33 = x_61;
x_34 = x_63;
x_35 = lean_box(0);
x_36 = x_59;
x_37 = x_57;
x_38 = x_77;
goto block_41;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec_ref(x_57);
lean_dec_ref(x_53);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec_ref(x_44);
lean_dec(x_42);
x_78 = lean_ctor_get(x_58, 0);
x_85 = !lean_is_exclusive(x_58);
if (x_85 == 0)
{
x_79 = x_58;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_58);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
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
lean_object* x_86; 
x_86 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_43, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_box(0);
x_89 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5);
x_90 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_50);
x_91 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_49);
x_92 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_53);
x_93 = lean_int_dec_le(x_42, x_47);
lean_dec(x_42);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_94 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14));
x_95 = l_Lean_Level_ofNat(x_48);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_88);
x_97 = l_Lean_Expr_const___override(x_94, x_96);
x_98 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_99 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_100 = lean_int_neg(x_47);
lean_dec(x_47);
x_101 = l_Int_toNat(x_100);
lean_dec(x_100);
x_102 = l_Lean_instToExprInt_mkNat(x_101);
x_103 = l_Lean_mkApp3(x_97, x_98, x_99, x_102);
x_18 = x_44;
x_19 = x_87;
x_20 = x_89;
x_21 = x_92;
x_22 = x_91;
x_23 = x_90;
x_24 = x_57;
x_25 = lean_box(0);
x_26 = x_103;
goto block_29;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Int_toNat(x_47);
lean_dec(x_47);
x_105 = l_Lean_instToExprInt_mkNat(x_104);
x_18 = x_44;
x_19 = x_87;
x_20 = x_89;
x_21 = x_92;
x_22 = x_91;
x_23 = x_90;
x_24 = x_57;
x_25 = lean_box(0);
x_26 = x_105;
goto block_29;
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_113; 
lean_dec_ref(x_57);
lean_dec_ref(x_53);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec_ref(x_44);
lean_dec(x_42);
x_106 = lean_ctor_get(x_86, 0);
x_113 = !lean_is_exclusive(x_86);
if (x_113 == 0)
{
x_107 = x_86;
x_108 = x_113;
goto block_112;
}
else
{
lean_inc(x_106);
lean_dec(x_86);
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
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_121; 
lean_dec_ref(x_53);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec_ref(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
block_179:
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = l_Int_Linear_Poly_gcdCoeffs_x27(x_126);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_dec_eq(x_130, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_133 = l_Int_Linear_Poly_getConst(x_126);
x_134 = lean_nat_to_int(x_130);
x_135 = lean_int_emod(x_133, x_134);
lean_dec(x_133);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_138 = lean_int_dec_eq(x_135, x_137);
lean_dec(x_135);
if (x_138 == 0)
{
uint8_t x_139; 
x_139 = 1;
x_42 = x_137;
x_43 = x_124;
x_44 = x_123;
x_45 = x_125;
x_46 = x_126;
x_47 = x_134;
x_48 = x_136;
x_49 = x_127;
x_50 = x_129;
x_51 = lean_box(0);
x_52 = x_139;
goto block_122;
}
else
{
x_42 = x_137;
x_43 = x_124;
x_44 = x_123;
x_45 = x_125;
x_46 = x_126;
x_47 = x_134;
x_48 = x_136;
x_49 = x_127;
x_50 = x_129;
x_51 = lean_box(0);
x_52 = x_132;
goto block_122;
}
}
else
{
lean_object* x_140; 
lean_dec(x_130);
lean_inc_ref(x_126);
x_140 = l_Int_Linear_Poly_denoteExpr___redArg(x_125, x_126);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_124, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_162; 
x_143 = lean_ctor_get(x_142, 0);
x_162 = !lean_is_exclusive(x_142);
if (x_162 == 0)
{
x_144 = x_142;
x_145 = x_162;
goto block_161;
}
else
{
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_box(0);
x_145 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_146 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
x_147 = l_Lean_mkIntLE(x_141, x_146);
x_148 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8);
x_149 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_129);
x_150 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_127);
x_151 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_126);
x_152 = l_Lean_eagerReflBoolTrue;
x_153 = l_Lean_mkApp5(x_148, x_143, x_149, x_150, x_151, x_152);
lean_inc_ref(x_147);
x_154 = l_Lean_mkPropEq(x_123, x_147);
x_155 = l_Lean_Meta_mkExpectedPropHint(x_153, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_147);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
if (x_145 == 0)
{
lean_ctor_set(x_144, 0, x_157);
x_158 = x_144;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_157);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_170; 
lean_dec(x_141);
lean_dec_ref(x_129);
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_123);
x_163 = lean_ctor_get(x_142, 0);
x_170 = !lean_is_exclusive(x_142);
if (x_170 == 0)
{
x_164 = x_142;
x_165 = x_170;
goto block_169;
}
else
{
lean_inc(x_163);
lean_dec(x_142);
x_164 = lean_box(0);
x_165 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_166; 
if (x_165 == 0)
{
x_166 = x_164;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_163);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_178; 
lean_dec_ref(x_129);
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_124);
lean_dec_ref(x_123);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_171 = lean_ctor_get(x_140, 0);
x_178 = !lean_is_exclusive(x_140);
if (x_178 == 0)
{
x_172 = x_140;
x_173 = x_178;
goto block_177;
}
else
{
lean_inc(x_171);
lean_dec(x_140);
x_172 = lean_box(0);
x_173 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_174; 
if (x_173 == 0)
{
x_174 = x_172;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_171);
x_174 = x_176;
goto block_175;
}
block_175:
{
return x_174;
}
}
}
}
}
block_319:
{
lean_object* x_182; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_182 = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_310; 
x_183 = lean_ctor_get(x_182, 0);
x_310 = !lean_is_exclusive(x_182);
if (x_310 == 0)
{
x_184 = x_182;
x_185 = x_310;
goto block_309;
}
else
{
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_box(0);
x_185 = x_310;
goto block_309;
}
block_309:
{
if (lean_obj_tag(x_183) == 1)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_304; 
lean_del_object(x_184);
x_186 = lean_ctor_get(x_183, 0);
x_304 = !lean_is_exclusive(x_183);
if (x_304 == 0)
{
x_187 = x_183;
x_188 = x_304;
goto block_303;
}
else
{
lean_inc(x_186);
lean_dec(x_183);
x_187 = lean_box(0);
x_188 = x_304;
goto block_303;
}
block_303:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_302; 
x_189 = lean_ctor_get(x_186, 1);
x_190 = lean_ctor_get(x_186, 0);
x_302 = !lean_is_exclusive(x_186);
if (x_302 == 0)
{
x_191 = x_186;
x_192 = x_302;
goto block_301;
}
else
{
lean_inc(x_189);
lean_inc(x_190);
lean_dec(x_186);
x_191 = lean_box(0);
x_192 = x_302;
goto block_301;
}
block_301:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_300; 
x_193 = lean_ctor_get(x_189, 0);
x_194 = lean_ctor_get(x_189, 1);
x_300 = !lean_is_exclusive(x_189);
if (x_300 == 0)
{
x_195 = x_189;
x_196 = x_300;
goto block_299;
}
else
{
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_189);
x_195 = lean_box(0);
x_196 = x_300;
goto block_299;
}
block_299:
{
lean_object* x_197; lean_object* x_198; 
lean_inc(x_194);
x_197 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_197, 0, x_180);
lean_closure_set(x_197, 1, x_194);
lean_inc(x_190);
lean_inc_ref(x_197);
x_198 = l_Int_Linear_Expr_denoteExpr___redArg(x_197, x_190);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec_ref(x_198);
lean_inc(x_193);
lean_inc_ref(x_197);
x_200 = l_Int_Linear_Expr_denoteExpr___redArg(x_197, x_193);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_282; 
x_201 = lean_ctor_get(x_200, 0);
x_282 = !lean_is_exclusive(x_200);
if (x_282 == 0)
{
x_202 = x_200;
x_203 = x_282;
goto block_281;
}
else
{
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_box(0);
x_203 = x_282;
goto block_281;
}
block_281:
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Lean_mkIntLE(x_199, x_201);
lean_inc(x_193);
lean_inc(x_190);
if (x_192 == 0)
{
lean_ctor_set_tag(x_191, 3);
lean_ctor_set(x_191, 1, x_193);
x_205 = x_191;
goto block_279;
}
else
{
lean_object* x_280; 
x_280 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_280, 0, x_190);
lean_ctor_set(x_280, 1, x_193);
x_205 = x_280;
goto block_279;
}
block_279:
{
lean_object* x_206; uint8_t x_207; 
x_206 = l_Int_Linear_Expr_norm(x_205);
lean_dec_ref(x_205);
x_207 = l_Int_Linear_Poly_isUnsatLe(x_206);
if (x_207 == 0)
{
uint8_t x_208; 
x_208 = l_Int_Linear_Poly_isValidLe(x_206);
if (x_208 == 0)
{
lean_del_object(x_195);
lean_del_object(x_187);
if (x_181 == 0)
{
lean_del_object(x_202);
x_123 = x_204;
x_124 = x_194;
x_125 = x_197;
x_126 = x_206;
x_127 = x_193;
x_128 = lean_box(0);
x_129 = x_190;
goto block_179;
}
else
{
lean_object* x_209; uint8_t x_210; 
lean_inc_ref(x_206);
x_209 = l_Int_Linear_Poly_toExpr(x_206);
x_210 = l_Int_Linear_instBEqExpr_beq(x_209, x_190);
lean_dec_ref(x_209);
if (x_210 == 0)
{
lean_del_object(x_202);
x_123 = x_204;
x_124 = x_194;
x_125 = x_197;
x_126 = x_206;
x_127 = x_193;
x_128 = lean_box(0);
x_129 = x_190;
goto block_179;
}
else
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35);
x_212 = l_Int_Linear_instBEqExpr_beq(x_193, x_211);
if (x_212 == 0)
{
lean_del_object(x_202);
x_123 = x_204;
x_124 = x_194;
x_125 = x_197;
x_126 = x_206;
x_127 = x_193;
x_128 = lean_box(0);
x_129 = x_190;
goto block_179;
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec_ref(x_206);
lean_dec_ref(x_204);
lean_dec_ref(x_197);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_190);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_213 = lean_box(0);
if (x_203 == 0)
{
lean_ctor_set(x_202, 0, x_213);
x_214 = x_202;
goto block_215;
}
else
{
lean_object* x_216; 
x_216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_216, 0, x_213);
x_214 = x_216;
goto block_215;
}
block_215:
{
return x_214;
}
}
}
}
}
else
{
lean_object* x_217; 
lean_dec_ref(x_206);
lean_del_object(x_202);
lean_dec_ref(x_197);
x_217 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_194, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; uint8_t x_239; 
x_218 = lean_ctor_get(x_217, 0);
x_239 = !lean_is_exclusive(x_217);
if (x_239 == 0)
{
x_219 = x_217;
x_220 = x_239;
goto block_238;
}
else
{
lean_inc(x_218);
lean_dec(x_217);
x_219 = lean_box(0);
x_220 = x_239;
goto block_238;
}
block_238:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_221 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38);
x_222 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11);
x_223 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_190);
x_224 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_193);
x_225 = l_Lean_eagerReflBoolTrue;
x_226 = l_Lean_mkApp4(x_222, x_218, x_223, x_224, x_225);
x_227 = l_Lean_mkPropEq(x_204, x_221);
x_228 = l_Lean_Meta_mkExpectedPropHint(x_226, x_227);
if (x_196 == 0)
{
lean_ctor_set(x_195, 1, x_228);
lean_ctor_set(x_195, 0, x_221);
x_229 = x_195;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_221);
lean_ctor_set(x_237, 1, x_228);
x_229 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_230; 
if (x_188 == 0)
{
lean_ctor_set(x_187, 0, x_229);
x_230 = x_187;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_229);
x_230 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_231; 
if (x_220 == 0)
{
lean_ctor_set(x_219, 0, x_230);
x_231 = x_219;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_230);
x_231 = x_233;
goto block_232;
}
block_232:
{
return x_231;
}
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_247; 
lean_dec_ref(x_204);
lean_del_object(x_195);
lean_dec(x_193);
lean_dec(x_190);
lean_del_object(x_187);
x_240 = lean_ctor_get(x_217, 0);
x_247 = !lean_is_exclusive(x_217);
if (x_247 == 0)
{
x_241 = x_217;
x_242 = x_247;
goto block_246;
}
else
{
lean_inc(x_240);
lean_dec(x_217);
x_241 = lean_box(0);
x_242 = x_247;
goto block_246;
}
block_246:
{
lean_object* x_243; 
if (x_242 == 0)
{
x_243 = x_241;
goto block_244;
}
else
{
lean_object* x_245; 
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_240);
x_243 = x_245;
goto block_244;
}
block_244:
{
return x_243;
}
}
}
}
}
else
{
lean_object* x_248; 
lean_dec_ref(x_206);
lean_del_object(x_202);
lean_dec_ref(x_197);
x_248 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_194, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_270; 
x_249 = lean_ctor_get(x_248, 0);
x_270 = !lean_is_exclusive(x_248);
if (x_270 == 0)
{
x_250 = x_248;
x_251 = x_270;
goto block_269;
}
else
{
lean_inc(x_249);
lean_dec(x_248);
x_250 = lean_box(0);
x_251 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_252 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
x_253 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14);
x_254 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_190);
x_255 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_193);
x_256 = l_Lean_eagerReflBoolTrue;
x_257 = l_Lean_mkApp4(x_253, x_249, x_254, x_255, x_256);
x_258 = l_Lean_mkPropEq(x_204, x_252);
x_259 = l_Lean_Meta_mkExpectedPropHint(x_257, x_258);
if (x_196 == 0)
{
lean_ctor_set(x_195, 1, x_259);
lean_ctor_set(x_195, 0, x_252);
x_260 = x_195;
goto block_267;
}
else
{
lean_object* x_268; 
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_252);
lean_ctor_set(x_268, 1, x_259);
x_260 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_261; 
if (x_188 == 0)
{
lean_ctor_set(x_187, 0, x_260);
x_261 = x_187;
goto block_265;
}
else
{
lean_object* x_266; 
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_260);
x_261 = x_266;
goto block_265;
}
block_265:
{
lean_object* x_262; 
if (x_251 == 0)
{
lean_ctor_set(x_250, 0, x_261);
x_262 = x_250;
goto block_263;
}
else
{
lean_object* x_264; 
x_264 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_264, 0, x_261);
x_262 = x_264;
goto block_263;
}
block_263:
{
return x_262;
}
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_278; 
lean_dec_ref(x_204);
lean_del_object(x_195);
lean_dec(x_193);
lean_dec(x_190);
lean_del_object(x_187);
x_271 = lean_ctor_get(x_248, 0);
x_278 = !lean_is_exclusive(x_248);
if (x_278 == 0)
{
x_272 = x_248;
x_273 = x_278;
goto block_277;
}
else
{
lean_inc(x_271);
lean_dec(x_248);
x_272 = lean_box(0);
x_273 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_274; 
if (x_273 == 0)
{
x_274 = x_272;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_271);
x_274 = x_276;
goto block_275;
}
block_275:
{
return x_274;
}
}
}
}
}
}
}
else
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; uint8_t x_290; 
lean_dec(x_199);
lean_dec_ref(x_197);
lean_del_object(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_del_object(x_191);
lean_dec(x_190);
lean_del_object(x_187);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_283 = lean_ctor_get(x_200, 0);
x_290 = !lean_is_exclusive(x_200);
if (x_290 == 0)
{
x_284 = x_200;
x_285 = x_290;
goto block_289;
}
else
{
lean_inc(x_283);
lean_dec(x_200);
x_284 = lean_box(0);
x_285 = x_290;
goto block_289;
}
block_289:
{
lean_object* x_286; 
if (x_285 == 0)
{
x_286 = x_284;
goto block_287;
}
else
{
lean_object* x_288; 
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_283);
x_286 = x_288;
goto block_287;
}
block_287:
{
return x_286;
}
}
}
}
else
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; uint8_t x_298; 
lean_dec_ref(x_197);
lean_del_object(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_del_object(x_191);
lean_dec(x_190);
lean_del_object(x_187);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_291 = lean_ctor_get(x_198, 0);
x_298 = !lean_is_exclusive(x_198);
if (x_298 == 0)
{
x_292 = x_198;
x_293 = x_298;
goto block_297;
}
else
{
lean_inc(x_291);
lean_dec(x_198);
x_292 = lean_box(0);
x_293 = x_298;
goto block_297;
}
block_297:
{
lean_object* x_294; 
if (x_293 == 0)
{
x_294 = x_292;
goto block_295;
}
else
{
lean_object* x_296; 
x_296 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_296, 0, x_291);
x_294 = x_296;
goto block_295;
}
block_295:
{
return x_294;
}
}
}
}
}
}
}
else
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_183);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_305 = lean_box(0);
if (x_185 == 0)
{
lean_ctor_set(x_184, 0, x_305);
x_306 = x_184;
goto block_307;
}
else
{
lean_object* x_308; 
x_308 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_308, 0, x_305);
x_306 = x_308;
goto block_307;
}
block_307:
{
return x_306;
}
}
}
}
else
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; uint8_t x_318; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_311 = lean_ctor_get(x_182, 0);
x_318 = !lean_is_exclusive(x_182);
if (x_318 == 0)
{
x_312 = x_182;
x_313 = x_318;
goto block_317;
}
else
{
lean_inc(x_311);
lean_dec(x_182);
x_312 = lean_box(0);
x_313 = x_318;
goto block_317;
}
block_317:
{
lean_object* x_314; 
if (x_313 == 0)
{
x_314 = x_312;
goto block_315;
}
else
{
lean_object* x_316; 
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_311);
x_314 = x_316;
goto block_315;
}
block_315:
{
return x_314;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelOne;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7));
x_55 = lean_unsigned_to_nat(1u);
x_56 = l_Lean_Expr_isAppOfArity(x_1, x_54, x_55);
if (x_56 == 0)
{
uint8_t x_57; lean_object* x_58; 
x_57 = 1;
x_58 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_57, x_2, x_3, x_4, x_5);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lean_Expr_appArg_x21(x_1);
x_60 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_59, x_3);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = l_Lean_Expr_cleanupAnnotations(x_61);
x_63 = l_Lean_Expr_isApp(x_62);
if (x_63 == 0)
{
lean_dec_ref(x_62);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_64);
x_65 = l_Lean_Expr_appFnCleanup___redArg(x_62);
x_66 = l_Lean_Expr_isApp(x_65);
if (x_66 == 0)
{
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc_ref(x_67);
x_68 = l_Lean_Expr_appFnCleanup___redArg(x_65);
x_69 = l_Lean_Expr_isApp(x_68);
if (x_69 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = l_Lean_Expr_appFnCleanup___redArg(x_68);
x_71 = l_Lean_Expr_isApp(x_70);
if (x_71 == 0)
{
lean_dec_ref(x_70);
lean_dec_ref(x_67);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_70, 1);
lean_inc_ref(x_72);
x_73 = l_Lean_Expr_appFnCleanup___redArg(x_70);
x_74 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10));
x_75 = l_Lean_Expr_isConstOf(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13));
x_77 = l_Lean_Expr_isConstOf(x_73, x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16));
x_79 = l_Lean_Expr_isConstOf(x_73, x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
x_81 = l_Lean_Expr_isConstOf(x_73, x_80);
lean_dec_ref(x_73);
if (x_81 == 0)
{
lean_dec_ref(x_72);
lean_dec_ref(x_67);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_82; 
x_82 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_72, x_3);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = l_Lean_Expr_cleanupAnnotations(x_83);
x_85 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
x_86 = l_Lean_Expr_isConstOf(x_84, x_85);
lean_dec_ref(x_84);
if (x_86 == 0)
{
lean_dec_ref(x_67);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17);
lean_inc_ref(x_64);
x_88 = l_Lean_mkIntAdd(x_64, x_87);
lean_inc_ref(x_67);
x_89 = l_Lean_mkIntLE(x_88, x_67);
x_90 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20);
x_91 = l_Lean_mkAppB(x_90, x_67, x_64);
x_11 = x_89;
x_12 = x_91;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_53;
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_dec_ref(x_67);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_92 = lean_ctor_get(x_82, 0);
x_99 = !lean_is_exclusive(x_82);
if (x_99 == 0)
{
x_93 = x_82;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_82);
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
else
{
lean_object* x_100; 
lean_dec_ref(x_73);
x_100 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_72, x_3);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = l_Lean_Expr_cleanupAnnotations(x_101);
x_103 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
x_104 = l_Lean_Expr_isConstOf(x_102, x_103);
lean_dec_ref(x_102);
if (x_104 == 0)
{
lean_dec_ref(x_67);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17);
lean_inc_ref(x_67);
x_106 = l_Lean_mkIntAdd(x_67, x_105);
lean_inc_ref(x_64);
x_107 = l_Lean_mkIntLE(x_106, x_64);
x_108 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23);
x_109 = l_Lean_mkAppB(x_108, x_67, x_64);
x_11 = x_107;
x_12 = x_109;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_53;
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_117; 
lean_dec_ref(x_67);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_110 = lean_ctor_get(x_100, 0);
x_117 = !lean_is_exclusive(x_100);
if (x_117 == 0)
{
x_111 = x_100;
x_112 = x_117;
goto block_116;
}
else
{
lean_inc(x_110);
lean_dec(x_100);
x_111 = lean_box(0);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_112 == 0)
{
x_113 = x_111;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_110);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
}
else
{
lean_object* x_118; 
lean_dec_ref(x_73);
x_118 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_72, x_3);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = l_Lean_Expr_cleanupAnnotations(x_119);
x_121 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
x_122 = l_Lean_Expr_isConstOf(x_120, x_121);
lean_dec_ref(x_120);
if (x_122 == 0)
{
lean_dec_ref(x_67);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_inc_ref(x_67);
lean_inc_ref(x_64);
x_123 = l_Lean_mkIntLE(x_64, x_67);
x_124 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26);
x_125 = l_Lean_mkAppB(x_124, x_67, x_64);
x_11 = x_123;
x_12 = x_125;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_53;
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_133; 
lean_dec_ref(x_67);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_126 = lean_ctor_get(x_118, 0);
x_133 = !lean_is_exclusive(x_118);
if (x_133 == 0)
{
x_127 = x_118;
x_128 = x_133;
goto block_132;
}
else
{
lean_inc(x_126);
lean_dec(x_118);
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
lean_object* x_134; 
lean_dec_ref(x_73);
x_134 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_72, x_3);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = l_Lean_Expr_cleanupAnnotations(x_135);
x_137 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
x_138 = l_Lean_Expr_isConstOf(x_136, x_137);
lean_dec_ref(x_136);
if (x_138 == 0)
{
lean_dec_ref(x_67);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_inc_ref(x_64);
lean_inc_ref(x_67);
x_139 = l_Lean_mkIntLE(x_67, x_64);
x_140 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29);
x_141 = l_Lean_mkAppB(x_140, x_67, x_64);
x_11 = x_139;
x_12 = x_141;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_53;
}
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; uint8_t x_149; 
lean_dec_ref(x_67);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_142 = lean_ctor_get(x_134, 0);
x_149 = !lean_is_exclusive(x_134);
if (x_149 == 0)
{
x_143 = x_134;
x_144 = x_149;
goto block_148;
}
else
{
lean_inc(x_142);
lean_dec(x_134);
x_143 = lean_box(0);
x_144 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_145; 
if (x_144 == 0)
{
x_145 = x_143;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_142);
x_145 = x_147;
goto block_146;
}
block_146:
{
return x_145;
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
lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_157; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_150 = lean_ctor_get(x_60, 0);
x_157 = !lean_is_exclusive(x_60);
if (x_157 == 0)
{
x_151 = x_60;
x_152 = x_157;
goto block_156;
}
else
{
lean_inc(x_150);
lean_dec(x_60);
x_151 = lean_box(0);
x_152 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_153; 
if (x_152 == 0)
{
x_153 = x_151;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_150);
x_153 = x_155;
goto block_154;
}
block_154:
{
return x_153;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
block_53:
{
uint8_t x_18; lean_object* x_19; 
x_18 = 0;
lean_inc_ref(x_11);
x_19 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_11, x_18, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_52; 
x_20 = lean_ctor_get(x_19, 0);
x_52 = !lean_is_exclusive(x_19);
if (x_52 == 0)
{
x_21 = x_19;
x_22 = x_52;
goto block_51;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_52;
goto block_51;
}
block_51:
{
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_45; 
x_23 = lean_ctor_get(x_20, 0);
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
x_24 = x_20;
x_25 = x_45;
goto block_44;
}
else
{
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_43; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
x_43 = !lean_is_exclusive(x_23);
if (x_43 == 0)
{
x_28 = x_23;
x_29 = x_43;
goto block_42;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4);
x_31 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5);
lean_inc(x_26);
x_32 = l_Lean_mkApp6(x_30, x_31, x_1, x_11, x_26, x_12, x_27);
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_32);
x_33 = x_28;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_32);
x_33 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_34; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_33);
x_34 = x_24;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_33);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_34);
x_35 = x_21;
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
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_20);
lean_dec_ref(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_11);
lean_ctor_set(x_46, 1, x_12);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_47);
x_48 = x_21;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_47);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
else
{
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_1);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_30; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_30 = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_199; 
x_31 = lean_ctor_get(x_30, 0);
x_199 = !lean_is_exclusive(x_30);
if (x_199 == 0)
{
x_32 = x_30;
x_33 = x_199;
goto block_198;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_199;
goto block_198;
}
block_198:
{
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_193; 
x_34 = lean_ctor_get(x_31, 0);
x_193 = !lean_is_exclusive(x_31);
if (x_193 == 0)
{
x_35 = x_31;
x_36 = x_193;
goto block_192;
}
else
{
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = x_193;
goto block_192;
}
block_192:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_191; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_191 = !lean_is_exclusive(x_37);
if (x_191 == 0)
{
x_41 = x_37;
x_42 = x_191;
goto block_190;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_box(0);
x_42 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_93; 
x_43 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
x_93 = lean_int_dec_eq(x_38, x_43);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_del_object(x_32);
x_94 = l_Lean_instInhabitedExpr;
lean_inc(x_40);
x_95 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_95, 0, x_94);
lean_closure_set(x_95, 1, x_40);
lean_inc(x_39);
lean_inc_ref(x_95);
x_96 = l_Int_Linear_Expr_denoteExpr___redArg(x_95, x_39);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_177; 
x_97 = lean_ctor_get(x_96, 0);
x_177 = !lean_is_exclusive(x_96);
if (x_177 == 0)
{
x_98 = x_96;
x_99 = x_177;
goto block_176;
}
else
{
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_box(0);
x_99 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_100; uint8_t x_166; 
x_166 = lean_int_dec_le(x_43, x_38);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_168 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_169 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_170 = lean_int_neg(x_38);
x_171 = l_Int_toNat(x_170);
lean_dec(x_170);
x_172 = l_Lean_instToExprInt_mkNat(x_171);
x_173 = l_Lean_mkApp3(x_167, x_168, x_169, x_172);
x_100 = x_173;
goto block_165;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = l_Int_toNat(x_38);
x_175 = l_Lean_instToExprInt_mkNat(x_174);
x_100 = x_175;
goto block_165;
}
block_165:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_inc_ref(x_100);
x_101 = l_Lean_mkIntDvd(x_100, x_97);
x_102 = l_Int_Linear_Expr_norm(x_39);
lean_inc(x_38);
x_103 = l_Int_Linear_Poly_gcdCoeffs(x_102, x_38);
x_104 = l_Int_Linear_Poly_getConst(x_102);
x_105 = lean_int_emod(x_104, x_103);
lean_dec(x_104);
x_106 = lean_int_dec_eq(x_105, x_43);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_103);
lean_dec_ref(x_102);
lean_del_object(x_98);
lean_dec_ref(x_95);
lean_dec(x_38);
x_107 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_40, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_128; 
x_108 = lean_ctor_get(x_107, 0);
x_128 = !lean_is_exclusive(x_107);
if (x_128 == 0)
{
x_109 = x_107;
x_110 = x_128;
goto block_127;
}
else
{
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_box(0);
x_110 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_111 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
x_112 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8);
x_113 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_39);
x_114 = l_Lean_eagerReflBoolTrue;
x_115 = l_Lean_mkApp4(x_112, x_108, x_100, x_113, x_114);
x_116 = l_Lean_mkPropEq(x_101, x_111);
x_117 = l_Lean_Meta_mkExpectedPropHint(x_115, x_116);
if (x_42 == 0)
{
lean_ctor_set(x_41, 1, x_117);
lean_ctor_set(x_41, 0, x_111);
x_118 = x_41;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_111);
lean_ctor_set(x_126, 1, x_117);
x_118 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_119; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_118);
x_119 = x_35;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_118);
x_119 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_120; 
if (x_110 == 0)
{
lean_ctor_set(x_109, 0, x_119);
x_120 = x_109;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_119);
x_120 = x_122;
goto block_121;
}
block_121:
{
return x_120;
}
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_136; 
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_del_object(x_41);
lean_dec(x_39);
lean_del_object(x_35);
x_129 = lean_ctor_get(x_107, 0);
x_136 = !lean_is_exclusive(x_107);
if (x_136 == 0)
{
x_130 = x_107;
x_131 = x_136;
goto block_135;
}
else
{
lean_inc(x_129);
lean_dec(x_107);
x_130 = lean_box(0);
x_131 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_132; 
if (x_131 == 0)
{
x_132 = x_130;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_129);
x_132 = x_134;
goto block_133;
}
block_133:
{
return x_132;
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_del_object(x_41);
lean_del_object(x_35);
x_137 = l_Int_Linear_Poly_div(x_103, x_102);
lean_inc_ref(x_137);
x_138 = l_Int_Linear_Poly_toExpr(x_137);
x_139 = l_Int_Linear_instBEqExpr_beq(x_39, x_138);
lean_dec_ref(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
lean_del_object(x_98);
lean_inc_ref(x_137);
x_140 = l_Int_Linear_Poly_denoteExpr___redArg(x_95, x_137);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_int_ediv(x_38, x_103);
lean_dec(x_38);
x_143 = lean_int_dec_le(x_43, x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_144 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_145 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_146 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_147 = lean_int_neg(x_142);
lean_dec(x_142);
x_148 = l_Int_toNat(x_147);
lean_dec(x_147);
x_149 = l_Lean_instToExprInt_mkNat(x_148);
x_150 = l_Lean_mkApp3(x_144, x_145, x_146, x_149);
x_44 = x_100;
x_45 = x_103;
x_46 = x_101;
x_47 = x_141;
x_48 = x_137;
x_49 = lean_box(0);
x_50 = x_150;
goto block_92;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = l_Int_toNat(x_142);
lean_dec(x_142);
x_152 = l_Lean_instToExprInt_mkNat(x_151);
x_44 = x_100;
x_45 = x_103;
x_46 = x_101;
x_47 = x_141;
x_48 = x_137;
x_49 = lean_box(0);
x_50 = x_152;
goto block_92;
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_160; 
lean_dec_ref(x_137);
lean_dec(x_103);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_153 = lean_ctor_get(x_140, 0);
x_160 = !lean_is_exclusive(x_140);
if (x_160 == 0)
{
x_154 = x_140;
x_155 = x_160;
goto block_159;
}
else
{
lean_inc(x_153);
lean_dec(x_140);
x_154 = lean_box(0);
x_155 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_156; 
if (x_155 == 0)
{
x_156 = x_154;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_153);
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
lean_object* x_161; lean_object* x_162; 
lean_dec_ref(x_137);
lean_dec(x_103);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_95);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_161 = lean_box(0);
if (x_99 == 0)
{
lean_ctor_set(x_98, 0, x_161);
x_162 = x_98;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_161);
x_162 = x_164;
goto block_163;
}
block_163:
{
return x_162;
}
}
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_185; 
lean_dec_ref(x_95);
lean_del_object(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_del_object(x_35);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_178 = lean_ctor_get(x_96, 0);
x_185 = !lean_is_exclusive(x_96);
if (x_185 == 0)
{
x_179 = x_96;
x_180 = x_185;
goto block_184;
}
else
{
lean_inc(x_178);
lean_dec(x_96);
x_179 = lean_box(0);
x_180 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_181; 
if (x_180 == 0)
{
x_181 = x_179;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_178);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_del_object(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_del_object(x_35);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_186 = lean_box(0);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_186);
x_187 = x_32;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_186);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
block_92:
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_inc_ref(x_50);
x_51 = l_Lean_mkIntDvd(x_50, x_47);
x_52 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
x_53 = lean_int_dec_eq(x_45, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_40, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2);
x_57 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_39);
x_58 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_48);
x_59 = lean_int_dec_le(x_43, x_45);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
x_61 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
x_62 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
x_63 = lean_int_neg(x_45);
lean_dec(x_45);
x_64 = l_Int_toNat(x_63);
lean_dec(x_63);
x_65 = l_Lean_instToExprInt_mkNat(x_64);
x_66 = l_Lean_mkApp3(x_60, x_61, x_62, x_65);
x_17 = x_56;
x_18 = x_44;
x_19 = lean_box(0);
x_20 = x_46;
x_21 = x_55;
x_22 = x_58;
x_23 = x_50;
x_24 = x_51;
x_25 = x_57;
x_26 = x_66;
goto block_29;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Int_toNat(x_45);
lean_dec(x_45);
x_68 = l_Lean_instToExprInt_mkNat(x_67);
x_17 = x_56;
x_18 = x_44;
x_19 = lean_box(0);
x_20 = x_46;
x_21 = x_55;
x_22 = x_58;
x_23 = x_50;
x_24 = x_51;
x_25 = x_57;
x_26 = x_68;
goto block_29;
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_76; 
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_48);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_39);
x_69 = lean_ctor_get(x_54, 0);
x_76 = !lean_is_exclusive(x_54);
if (x_76 == 0)
{
x_70 = x_54;
x_71 = x_76;
goto block_75;
}
else
{
lean_inc(x_69);
lean_dec(x_54);
x_70 = lean_box(0);
x_71 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_72; 
if (x_71 == 0)
{
x_72 = x_70;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_69);
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
lean_object* x_77; 
lean_dec_ref(x_50);
lean_dec(x_45);
x_77 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_40, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5);
x_80 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_39);
x_81 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_48);
x_82 = l_Lean_eagerReflBoolTrue;
x_83 = l_Lean_mkApp5(x_79, x_78, x_44, x_80, x_81, x_82);
x_7 = x_46;
x_8 = x_51;
x_9 = x_83;
x_10 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec_ref(x_51);
lean_dec_ref(x_48);
lean_dec_ref(x_46);
lean_dec_ref(x_44);
lean_dec(x_39);
x_84 = lean_ctor_get(x_77, 0);
x_91 = !lean_is_exclusive(x_77);
if (x_91 == 0)
{
x_85 = x_77;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_77);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
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
lean_object* x_194; lean_object* x_195; 
lean_dec(x_31);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_194 = lean_box(0);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_194);
x_195 = x_32;
goto block_196;
}
else
{
lean_object* x_197; 
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_194);
x_195 = x_197;
goto block_196;
}
block_196:
{
return x_195;
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_207; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_200 = lean_ctor_get(x_30, 0);
x_207 = !lean_is_exclusive(x_30);
if (x_207 == 0)
{
x_201 = x_30;
x_202 = x_207;
goto block_206;
}
else
{
lean_inc(x_200);
lean_dec(x_30);
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
block_16:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_8);
x_11 = l_Lean_mkPropEq(x_7, x_8);
x_12 = l_Lean_Meta_mkExpectedPropHint(x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_eagerReflBoolTrue;
x_28 = l_Lean_mkApp7(x_17, x_21, x_18, x_25, x_23, x_22, x_26, x_27);
x_7 = x_20;
x_8 = x_24;
x_9 = x_28;
x_10 = lean_box(0);
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_instInhabitedExpr;
x_4 = lean_array_get_borrowed(x_3, x_1, x_2);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_74; 
x_8 = lean_ctor_get(x_7, 0);
x_74 = !lean_is_exclusive(x_7);
if (x_74 == 0)
{
x_9 = x_7;
x_10 = x_74;
goto block_73;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_72; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_72 = !lean_is_exclusive(x_8);
if (x_72 == 0)
{
x_13 = x_8;
x_14 = x_72;
goto block_71;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Int_Linear_Expr_norm(x_11);
lean_inc_ref(x_15);
x_16 = l_Int_Linear_Poly_toExpr(x_15);
x_17 = l_Int_Linear_instBEqExpr_beq(x_11, x_16);
lean_dec_ref(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_del_object(x_9);
lean_inc(x_12);
x_18 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_12, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_20, 0, x_12);
lean_inc(x_11);
x_21 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_11);
lean_inc_ref(x_20);
x_22 = l_Int_Linear_Expr_denoteExpr___redArg(x_20, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc_ref(x_15);
x_24 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_15);
x_25 = l_Int_Linear_Poly_denoteExpr___redArg(x_20, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_42; 
x_26 = lean_ctor_get(x_25, 0);
x_42 = !lean_is_exclusive(x_25);
if (x_42 == 0)
{
x_27 = x_25;
x_28 = x_42;
goto block_41;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3);
x_30 = l_Lean_eagerReflBoolTrue;
x_31 = l_Lean_mkApp4(x_29, x_19, x_21, x_24, x_30);
lean_inc(x_26);
x_32 = l_Lean_mkIntEq(x_23, x_26);
x_33 = l_Lean_Meta_mkExpectedPropHint(x_31, x_32);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_33);
lean_ctor_set(x_13, 0, x_26);
x_34 = x_13;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_33);
x_34 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_35);
x_36 = x_27;
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
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec(x_19);
lean_del_object(x_13);
x_43 = lean_ctor_get(x_25, 0);
x_50 = !lean_is_exclusive(x_25);
if (x_50 == 0)
{
x_44 = x_25;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_25);
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
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_15);
lean_del_object(x_13);
x_51 = lean_ctor_get(x_22, 0);
x_58 = !lean_is_exclusive(x_22);
if (x_58 == 0)
{
x_52 = x_22;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_22);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec_ref(x_15);
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_59 = lean_ctor_get(x_18, 0);
x_66 = !lean_is_exclusive(x_18);
if (x_66 == 0)
{
x_60 = x_18;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_18);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_15);
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_67 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_67);
x_68 = x_9;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_75 = lean_ctor_get(x_7, 0);
x_82 = !lean_is_exclusive(x_7);
if (x_82 == 0)
{
x_76 = x_7;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_7);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
}
#ifdef __cplusplus
}
#endif
