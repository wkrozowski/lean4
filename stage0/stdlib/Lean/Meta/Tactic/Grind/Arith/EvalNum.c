// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.EvalNum
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.IntInstTesters import Lean.Meta.NatInstTesters
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_checkExp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exponent "};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__1_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_checkExp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = " exceeds threshold for exponentiation `(exp := "};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_checkExp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_checkExp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__6;
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAbs"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 186, 174, 182, 213, 167, 94, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value),LEAN_SCALAR_PTR_LITERAL(147, 74, 209, 32, 95, 50, 220, 192)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 237, 167, 212, 100, 179, 19, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_89; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_19 = lean_ctor_get(x_18, 0);
x_89 = !lean_is_exclusive(x_18);
if (x_89 == 0)
{
x_20 = x_18;
x_21 = x_89;
goto block_88;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_22, 7);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_nat_dec_lt(x_23, x_1);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__0));
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_25);
x_26 = x_20;
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
else
{
lean_object* x_29; 
lean_del_object(x_20);
x_29 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_79; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_32 = lean_ctor_get(x_31, 0);
x_79 = !lean_is_exclusive(x_31);
if (x_79 == 0)
{
x_33 = x_31;
x_34 = x_79;
goto block_78;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_77; 
x_35 = lean_ctor_get(x_32, 0);
x_77 = !lean_is_exclusive(x_32);
if (x_77 == 0)
{
x_36 = x_32;
x_37 = x_77;
goto block_76;
}
else
{
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = x_77;
goto block_76;
}
block_76:
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_35, sizeof(void*)*11 + 14);
lean_dec(x_35);
if (x_38 == 0)
{
lean_del_object(x_36);
lean_del_object(x_33);
lean_dec(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_ctor_get(x_40, 7);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___closed__2, &l_Lean_Meta_Grind_Arith_checkExp___closed__2_once, _init_l_Lean_Meta_Grind_Arith_checkExp___closed__2);
x_43 = l_Nat_reprFast(x_1);
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 3);
lean_ctor_set(x_36, 0, x_43);
x_44 = x_36;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_43);
x_44 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = l_Lean_MessageData_ofFormat(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___closed__4, &l_Lean_Meta_Grind_Arith_checkExp___closed__4_once, _init_l_Lean_Meta_Grind_Arith_checkExp___closed__4);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Nat_reprFast(x_41);
if (x_34 == 0)
{
lean_ctor_set_tag(x_33, 3);
lean_ctor_set(x_33, 0, x_49);
x_50 = x_33;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_49);
x_50 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = l_Lean_MessageData_ofFormat(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___closed__6, &l_Lean_Meta_Grind_Arith_checkExp___closed__6_once, _init_l_Lean_Meta_Grind_Arith_checkExp___closed__6);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Meta_Grind_reportIssue(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
x_56 = lean_ctor_get(x_55, 0);
x_63 = !lean_is_exclusive(x_55);
if (x_63 == 0)
{
x_57 = x_55;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_del_object(x_36);
lean_del_object(x_33);
lean_dec(x_1);
x_68 = lean_ctor_get(x_39, 0);
x_75 = !lean_is_exclusive(x_39);
if (x_75 == 0)
{
x_69 = x_39;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_39);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_87; 
lean_dec(x_1);
x_80 = lean_ctor_get(x_29, 0);
x_87 = !lean_is_exclusive(x_29);
if (x_87 == 0)
{
x_81 = x_29;
x_82 = x_87;
goto block_86;
}
else
{
lean_inc(x_80);
lean_dec(x_29);
x_81 = lean_box(0);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
if (x_82 == 0)
{
x_83 = x_81;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_80);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec(x_1);
x_90 = lean_ctor_get(x_16, 0);
x_97 = !lean_is_exclusive(x_16);
if (x_97 == 0)
{
x_91 = x_16;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_16);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_checkExp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_68; 
lean_inc_ref(x_1);
x_68 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_439; 
x_69 = lean_ctor_get(x_68, 0);
x_439 = !lean_is_exclusive(x_68);
if (x_439 == 0)
{
x_70 = x_68;
x_71 = x_439;
goto block_438;
}
else
{
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = x_439;
goto block_438;
}
block_438:
{
lean_object* x_77; uint8_t x_78; 
x_77 = l_Lean_Expr_cleanupAnnotations(x_69);
x_78 = l_Lean_Expr_isApp(x_77);
if (x_78 == 0)
{
lean_dec_ref(x_77);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_76;
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_79);
x_80 = l_Lean_Expr_appFnCleanup___redArg(x_77);
x_81 = l_Lean_Expr_isApp(x_80);
if (x_81 == 0)
{
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_76;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_80, 1);
lean_inc_ref(x_82);
x_83 = l_Lean_Expr_appFnCleanup___redArg(x_80);
x_84 = l_Lean_Expr_isApp(x_83);
if (x_84 == 0)
{
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_76;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_83, 1);
lean_inc_ref(x_85);
x_86 = l_Lean_Expr_appFnCleanup___redArg(x_83);
x_87 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3));
x_88 = l_Lean_Expr_isConstOf(x_86, x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6));
x_90 = l_Lean_Expr_isConstOf(x_86, x_89);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12));
x_92 = l_Lean_Expr_isConstOf(x_86, x_91);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
lean_dec_ref(x_1);
x_93 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9));
x_94 = l_Lean_Expr_isConstOf(x_86, x_93);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = l_Lean_Expr_isApp(x_86);
if (x_95 == 0)
{
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_76;
}
else
{
lean_object* x_96; uint8_t x_97; 
x_96 = l_Lean_Expr_appFnCleanup___redArg(x_86);
x_97 = l_Lean_Expr_isApp(x_96);
if (x_97 == 0)
{
lean_dec_ref(x_96);
lean_dec_ref(x_85);
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_76;
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = l_Lean_Expr_appFnCleanup___redArg(x_96);
x_99 = l_Lean_Expr_isApp(x_98);
if (x_99 == 0)
{
lean_dec_ref(x_98);
lean_dec_ref(x_85);
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_76;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = l_Lean_Expr_appFnCleanup___redArg(x_98);
x_101 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15));
x_102 = l_Lean_Expr_isConstOf(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18));
x_104 = l_Lean_Expr_isConstOf(x_100, x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21));
x_106 = l_Lean_Expr_isConstOf(x_100, x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27));
x_108 = l_Lean_Expr_isConstOf(x_100, x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24));
x_110 = l_Lean_Expr_isConstOf(x_100, x_109);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30));
x_112 = l_Lean_Expr_isConstOf(x_100, x_111);
lean_dec_ref(x_100);
if (x_112 == 0)
{
lean_dec_ref(x_85);
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_76;
}
else
{
lean_object* x_113; 
lean_del_object(x_70);
x_113 = l_Lean_Meta_Structural_isInstHAddInt___redArg(x_85, x_8);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_145; 
x_114 = lean_ctor_get(x_113, 0);
x_145 = !lean_is_exclusive(x_113);
if (x_145 == 0)
{
x_115 = x_113;
x_116 = x_145;
goto block_144;
}
else
{
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_box(0);
x_116 = x_145;
goto block_144;
}
block_144:
{
uint8_t x_117; 
x_117 = lean_unbox(x_114);
lean_dec(x_114);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_118 = lean_box(0);
if (x_116 == 0)
{
lean_ctor_set(x_115, 0, x_118);
x_119 = x_115;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_118);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
else
{
lean_object* x_122; 
lean_del_object(x_115);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_122;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec_ref(x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_dec(x_124);
return x_125;
}
else
{
lean_object* x_127; uint8_t x_128; uint8_t x_142; 
x_142 = !lean_is_exclusive(x_125);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_125, 0);
lean_dec(x_143);
x_127 = x_125;
x_128 = x_142;
goto block_141;
}
else
{
lean_dec(x_125);
x_127 = lean_box(0);
x_128 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_140; 
x_129 = lean_ctor_get(x_126, 0);
x_140 = !lean_is_exclusive(x_126);
if (x_140 == 0)
{
x_130 = x_126;
x_131 = x_140;
goto block_139;
}
else
{
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_box(0);
x_131 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_int_add(x_124, x_129);
lean_dec(x_129);
lean_dec(x_124);
if (x_131 == 0)
{
lean_ctor_set(x_130, 0, x_132);
x_133 = x_130;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_132);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_128 == 0)
{
lean_ctor_set(x_127, 0, x_133);
x_134 = x_127;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_133);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
}
}
else
{
lean_dec(x_124);
return x_125;
}
}
}
else
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_122;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_153; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_146 = lean_ctor_get(x_113, 0);
x_153 = !lean_is_exclusive(x_113);
if (x_153 == 0)
{
x_147 = x_113;
x_148 = x_153;
goto block_152;
}
else
{
lean_inc(x_146);
lean_dec(x_113);
x_147 = lean_box(0);
x_148 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_149; 
if (x_148 == 0)
{
x_149 = x_147;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_146);
x_149 = x_151;
goto block_150;
}
block_150:
{
return x_149;
}
}
}
}
}
else
{
lean_object* x_154; 
lean_dec_ref(x_100);
lean_del_object(x_70);
x_154 = l_Lean_Meta_Structural_isInstHSubInt___redArg(x_85, x_8);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_186; 
x_155 = lean_ctor_get(x_154, 0);
x_186 = !lean_is_exclusive(x_154);
if (x_186 == 0)
{
x_156 = x_154;
x_157 = x_186;
goto block_185;
}
else
{
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_box(0);
x_157 = x_186;
goto block_185;
}
block_185:
{
uint8_t x_158; 
x_158 = lean_unbox(x_155);
lean_dec(x_155);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_159 = lean_box(0);
if (x_157 == 0)
{
lean_ctor_set(x_156, 0, x_159);
x_160 = x_156;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_159);
x_160 = x_162;
goto block_161;
}
block_161:
{
return x_160;
}
}
else
{
lean_object* x_163; 
lean_del_object(x_156);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_163 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_163;
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec_ref(x_164);
x_166 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
lean_dec(x_165);
return x_166;
}
else
{
lean_object* x_168; uint8_t x_169; uint8_t x_183; 
x_183 = !lean_is_exclusive(x_166);
if (x_183 == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_166, 0);
lean_dec(x_184);
x_168 = x_166;
x_169 = x_183;
goto block_182;
}
else
{
lean_dec(x_166);
x_168 = lean_box(0);
x_169 = x_183;
goto block_182;
}
block_182:
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_181; 
x_170 = lean_ctor_get(x_167, 0);
x_181 = !lean_is_exclusive(x_167);
if (x_181 == 0)
{
x_171 = x_167;
x_172 = x_181;
goto block_180;
}
else
{
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_box(0);
x_172 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_int_sub(x_165, x_170);
lean_dec(x_170);
lean_dec(x_165);
if (x_172 == 0)
{
lean_ctor_set(x_171, 0, x_173);
x_174 = x_171;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_173);
x_174 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_175; 
if (x_169 == 0)
{
lean_ctor_set(x_168, 0, x_174);
x_175 = x_168;
goto block_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_174);
x_175 = x_177;
goto block_176;
}
block_176:
{
return x_175;
}
}
}
}
}
}
else
{
lean_dec(x_165);
return x_166;
}
}
}
else
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_163;
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_194; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_187 = lean_ctor_get(x_154, 0);
x_194 = !lean_is_exclusive(x_154);
if (x_194 == 0)
{
x_188 = x_154;
x_189 = x_194;
goto block_193;
}
else
{
lean_inc(x_187);
lean_dec(x_154);
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
else
{
lean_object* x_195; 
lean_dec_ref(x_100);
lean_del_object(x_70);
x_195 = l_Lean_Meta_Structural_isInstHMulInt___redArg(x_85, x_8);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_227; 
x_196 = lean_ctor_get(x_195, 0);
x_227 = !lean_is_exclusive(x_195);
if (x_227 == 0)
{
x_197 = x_195;
x_198 = x_227;
goto block_226;
}
else
{
lean_inc(x_196);
lean_dec(x_195);
x_197 = lean_box(0);
x_198 = x_227;
goto block_226;
}
block_226:
{
uint8_t x_199; 
x_199 = lean_unbox(x_196);
lean_dec(x_196);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_200 = lean_box(0);
if (x_198 == 0)
{
lean_ctor_set(x_197, 0, x_200);
x_201 = x_197;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_203, 0, x_200);
x_201 = x_203;
goto block_202;
}
block_202:
{
return x_201;
}
}
else
{
lean_object* x_204; 
lean_del_object(x_197);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_204 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_204;
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec_ref(x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec_ref(x_205);
x_207 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_dec(x_206);
return x_207;
}
else
{
lean_object* x_209; uint8_t x_210; uint8_t x_224; 
x_224 = !lean_is_exclusive(x_207);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_207, 0);
lean_dec(x_225);
x_209 = x_207;
x_210 = x_224;
goto block_223;
}
else
{
lean_dec(x_207);
x_209 = lean_box(0);
x_210 = x_224;
goto block_223;
}
block_223:
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_222; 
x_211 = lean_ctor_get(x_208, 0);
x_222 = !lean_is_exclusive(x_208);
if (x_222 == 0)
{
x_212 = x_208;
x_213 = x_222;
goto block_221;
}
else
{
lean_inc(x_211);
lean_dec(x_208);
x_212 = lean_box(0);
x_213 = x_222;
goto block_221;
}
block_221:
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_int_mul(x_206, x_211);
lean_dec(x_211);
lean_dec(x_206);
if (x_213 == 0)
{
lean_ctor_set(x_212, 0, x_214);
x_215 = x_212;
goto block_219;
}
else
{
lean_object* x_220; 
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_214);
x_215 = x_220;
goto block_219;
}
block_219:
{
lean_object* x_216; 
if (x_210 == 0)
{
lean_ctor_set(x_209, 0, x_215);
x_216 = x_209;
goto block_217;
}
else
{
lean_object* x_218; 
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_215);
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
}
else
{
lean_dec(x_206);
return x_207;
}
}
}
else
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_204;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_235; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_228 = lean_ctor_get(x_195, 0);
x_235 = !lean_is_exclusive(x_195);
if (x_235 == 0)
{
x_229 = x_195;
x_230 = x_235;
goto block_234;
}
else
{
lean_inc(x_228);
lean_dec(x_195);
x_229 = lean_box(0);
x_230 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_231; 
if (x_230 == 0)
{
x_231 = x_229;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_228);
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
lean_object* x_236; 
lean_dec_ref(x_100);
lean_del_object(x_70);
x_236 = l_Lean_Meta_Structural_isInstHDivInt___redArg(x_85, x_8);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_268; 
x_237 = lean_ctor_get(x_236, 0);
x_268 = !lean_is_exclusive(x_236);
if (x_268 == 0)
{
x_238 = x_236;
x_239 = x_268;
goto block_267;
}
else
{
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_box(0);
x_239 = x_268;
goto block_267;
}
block_267:
{
uint8_t x_240; 
x_240 = lean_unbox(x_237);
lean_dec(x_237);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_241 = lean_box(0);
if (x_239 == 0)
{
lean_ctor_set(x_238, 0, x_241);
x_242 = x_238;
goto block_243;
}
else
{
lean_object* x_244; 
x_244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_244, 0, x_241);
x_242 = x_244;
goto block_243;
}
block_243:
{
return x_242;
}
}
else
{
lean_object* x_245; 
lean_del_object(x_238);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_245 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
if (lean_obj_tag(x_246) == 0)
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_245;
}
else
{
lean_object* x_247; lean_object* x_248; 
lean_dec_ref(x_245);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_248 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_obj_tag(x_249) == 0)
{
lean_dec(x_247);
return x_248;
}
else
{
lean_object* x_250; uint8_t x_251; uint8_t x_265; 
x_265 = !lean_is_exclusive(x_248);
if (x_265 == 0)
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_248, 0);
lean_dec(x_266);
x_250 = x_248;
x_251 = x_265;
goto block_264;
}
else
{
lean_dec(x_248);
x_250 = lean_box(0);
x_251 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; uint8_t x_263; 
x_252 = lean_ctor_get(x_249, 0);
x_263 = !lean_is_exclusive(x_249);
if (x_263 == 0)
{
x_253 = x_249;
x_254 = x_263;
goto block_262;
}
else
{
lean_inc(x_252);
lean_dec(x_249);
x_253 = lean_box(0);
x_254 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_int_ediv(x_247, x_252);
lean_dec(x_252);
lean_dec(x_247);
if (x_254 == 0)
{
lean_ctor_set(x_253, 0, x_255);
x_256 = x_253;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_255);
x_256 = x_261;
goto block_260;
}
block_260:
{
lean_object* x_257; 
if (x_251 == 0)
{
lean_ctor_set(x_250, 0, x_256);
x_257 = x_250;
goto block_258;
}
else
{
lean_object* x_259; 
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_256);
x_257 = x_259;
goto block_258;
}
block_258:
{
return x_257;
}
}
}
}
}
}
else
{
lean_dec(x_247);
return x_248;
}
}
}
else
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_245;
}
}
}
}
else
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; uint8_t x_276; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_269 = lean_ctor_get(x_236, 0);
x_276 = !lean_is_exclusive(x_236);
if (x_276 == 0)
{
x_270 = x_236;
x_271 = x_276;
goto block_275;
}
else
{
lean_inc(x_269);
lean_dec(x_236);
x_270 = lean_box(0);
x_271 = x_276;
goto block_275;
}
block_275:
{
lean_object* x_272; 
if (x_271 == 0)
{
x_272 = x_270;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_269);
x_272 = x_274;
goto block_273;
}
block_273:
{
return x_272;
}
}
}
}
}
else
{
lean_object* x_277; 
lean_dec_ref(x_100);
lean_del_object(x_70);
x_277 = l_Lean_Meta_Structural_isInstHModInt___redArg(x_85, x_8);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; uint8_t x_309; 
x_278 = lean_ctor_get(x_277, 0);
x_309 = !lean_is_exclusive(x_277);
if (x_309 == 0)
{
x_279 = x_277;
x_280 = x_309;
goto block_308;
}
else
{
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_box(0);
x_280 = x_309;
goto block_308;
}
block_308:
{
uint8_t x_281; 
x_281 = lean_unbox(x_278);
lean_dec(x_278);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_282 = lean_box(0);
if (x_280 == 0)
{
lean_ctor_set(x_279, 0, x_282);
x_283 = x_279;
goto block_284;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_282);
x_283 = x_285;
goto block_284;
}
block_284:
{
return x_283;
}
}
else
{
lean_object* x_286; 
lean_del_object(x_279);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_286 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_286;
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec_ref(x_286);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
lean_dec_ref(x_287);
x_289 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
if (lean_obj_tag(x_290) == 0)
{
lean_dec(x_288);
return x_289;
}
else
{
lean_object* x_291; uint8_t x_292; uint8_t x_306; 
x_306 = !lean_is_exclusive(x_289);
if (x_306 == 0)
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_289, 0);
lean_dec(x_307);
x_291 = x_289;
x_292 = x_306;
goto block_305;
}
else
{
lean_dec(x_289);
x_291 = lean_box(0);
x_292 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; uint8_t x_304; 
x_293 = lean_ctor_get(x_290, 0);
x_304 = !lean_is_exclusive(x_290);
if (x_304 == 0)
{
x_294 = x_290;
x_295 = x_304;
goto block_303;
}
else
{
lean_inc(x_293);
lean_dec(x_290);
x_294 = lean_box(0);
x_295 = x_304;
goto block_303;
}
block_303:
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_int_emod(x_288, x_293);
lean_dec(x_293);
lean_dec(x_288);
if (x_295 == 0)
{
lean_ctor_set(x_294, 0, x_296);
x_297 = x_294;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_296);
x_297 = x_302;
goto block_301;
}
block_301:
{
lean_object* x_298; 
if (x_292 == 0)
{
lean_ctor_set(x_291, 0, x_297);
x_298 = x_291;
goto block_299;
}
else
{
lean_object* x_300; 
x_300 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_300, 0, x_297);
x_298 = x_300;
goto block_299;
}
block_299:
{
return x_298;
}
}
}
}
}
}
else
{
lean_dec(x_288);
return x_289;
}
}
}
else
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_286;
}
}
}
}
else
{
lean_object* x_310; lean_object* x_311; uint8_t x_312; uint8_t x_317; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_310 = lean_ctor_get(x_277, 0);
x_317 = !lean_is_exclusive(x_277);
if (x_317 == 0)
{
x_311 = x_277;
x_312 = x_317;
goto block_316;
}
else
{
lean_inc(x_310);
lean_dec(x_277);
x_311 = lean_box(0);
x_312 = x_317;
goto block_316;
}
block_316:
{
lean_object* x_313; 
if (x_312 == 0)
{
x_313 = x_311;
goto block_314;
}
else
{
lean_object* x_315; 
x_315 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_315, 0, x_310);
x_313 = x_315;
goto block_314;
}
block_314:
{
return x_313;
}
}
}
}
}
else
{
lean_object* x_318; 
lean_dec_ref(x_100);
lean_del_object(x_70);
x_318 = l_Lean_Meta_Structural_isInstHPowInt___redArg(x_85, x_8);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; uint8_t x_380; 
x_319 = lean_ctor_get(x_318, 0);
x_380 = !lean_is_exclusive(x_318);
if (x_380 == 0)
{
x_320 = x_318;
x_321 = x_380;
goto block_379;
}
else
{
lean_inc(x_319);
lean_dec(x_318);
x_320 = lean_box(0);
x_321 = x_380;
goto block_379;
}
block_379:
{
uint8_t x_322; 
x_322 = lean_unbox(x_319);
lean_dec(x_319);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_323 = lean_box(0);
if (x_321 == 0)
{
lean_ctor_set(x_320, 0, x_323);
x_324 = x_320;
goto block_325;
}
else
{
lean_object* x_326; 
x_326 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_326, 0, x_323);
x_324 = x_326;
goto block_325;
}
block_325:
{
return x_324;
}
}
else
{
lean_object* x_327; 
lean_del_object(x_320);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_327 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
if (lean_obj_tag(x_328) == 0)
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_327;
}
else
{
lean_object* x_329; lean_object* x_330; 
lean_dec_ref(x_327);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
lean_dec_ref(x_328);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_330 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; uint8_t x_370; 
x_331 = lean_ctor_get(x_330, 0);
x_370 = !lean_is_exclusive(x_330);
if (x_370 == 0)
{
x_332 = x_330;
x_333 = x_370;
goto block_369;
}
else
{
lean_inc(x_331);
lean_dec(x_330);
x_332 = lean_box(0);
x_333 = x_370;
goto block_369;
}
block_369:
{
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_329);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_334 = lean_box(0);
if (x_333 == 0)
{
lean_ctor_set(x_332, 0, x_334);
x_335 = x_332;
goto block_336;
}
else
{
lean_object* x_337; 
x_337 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_337, 0, x_334);
x_335 = x_337;
goto block_336;
}
block_336:
{
return x_335;
}
}
else
{
lean_object* x_338; lean_object* x_339; 
lean_del_object(x_332);
x_338 = lean_ctor_get(x_331, 0);
lean_inc(x_338);
lean_dec_ref(x_331);
lean_inc(x_338);
x_339 = l_Lean_Meta_Grind_Arith_checkExp(x_338, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; uint8_t x_342; uint8_t x_360; 
x_340 = lean_ctor_get(x_339, 0);
x_360 = !lean_is_exclusive(x_339);
if (x_360 == 0)
{
x_341 = x_339;
x_342 = x_360;
goto block_359;
}
else
{
lean_inc(x_340);
lean_dec(x_339);
x_341 = lean_box(0);
x_342 = x_360;
goto block_359;
}
block_359:
{
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_338);
lean_dec(x_329);
x_343 = lean_box(0);
if (x_342 == 0)
{
lean_ctor_set(x_341, 0, x_343);
x_344 = x_341;
goto block_345;
}
else
{
lean_object* x_346; 
x_346 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_346, 0, x_343);
x_344 = x_346;
goto block_345;
}
block_345:
{
return x_344;
}
}
else
{
lean_object* x_347; uint8_t x_348; uint8_t x_357; 
x_357 = !lean_is_exclusive(x_340);
if (x_357 == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_340, 0);
lean_dec(x_358);
x_347 = x_340;
x_348 = x_357;
goto block_356;
}
else
{
lean_dec(x_340);
x_347 = lean_box(0);
x_348 = x_357;
goto block_356;
}
block_356:
{
lean_object* x_349; lean_object* x_350; 
x_349 = l_Int_pow(x_329, x_338);
lean_dec(x_338);
lean_dec(x_329);
if (x_348 == 0)
{
lean_ctor_set(x_347, 0, x_349);
x_350 = x_347;
goto block_354;
}
else
{
lean_object* x_355; 
x_355 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_355, 0, x_349);
x_350 = x_355;
goto block_354;
}
block_354:
{
lean_object* x_351; 
if (x_342 == 0)
{
lean_ctor_set(x_341, 0, x_350);
x_351 = x_341;
goto block_352;
}
else
{
lean_object* x_353; 
x_353 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_353, 0, x_350);
x_351 = x_353;
goto block_352;
}
block_352:
{
return x_351;
}
}
}
}
}
}
else
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; uint8_t x_368; 
lean_dec(x_338);
lean_dec(x_329);
x_361 = lean_ctor_get(x_339, 0);
x_368 = !lean_is_exclusive(x_339);
if (x_368 == 0)
{
x_362 = x_339;
x_363 = x_368;
goto block_367;
}
else
{
lean_inc(x_361);
lean_dec(x_339);
x_362 = lean_box(0);
x_363 = x_368;
goto block_367;
}
block_367:
{
lean_object* x_364; 
if (x_363 == 0)
{
x_364 = x_362;
goto block_365;
}
else
{
lean_object* x_366; 
x_366 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_366, 0, x_361);
x_364 = x_366;
goto block_365;
}
block_365:
{
return x_364;
}
}
}
}
}
}
else
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; uint8_t x_378; 
lean_dec(x_329);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_371 = lean_ctor_get(x_330, 0);
x_378 = !lean_is_exclusive(x_330);
if (x_378 == 0)
{
x_372 = x_330;
x_373 = x_378;
goto block_377;
}
else
{
lean_inc(x_371);
lean_dec(x_330);
x_372 = lean_box(0);
x_373 = x_378;
goto block_377;
}
block_377:
{
lean_object* x_374; 
if (x_373 == 0)
{
x_374 = x_372;
goto block_375;
}
else
{
lean_object* x_376; 
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_371);
x_374 = x_376;
goto block_375;
}
block_375:
{
return x_374;
}
}
}
}
}
else
{
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_327;
}
}
}
}
else
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; uint8_t x_388; 
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_381 = lean_ctor_get(x_318, 0);
x_388 = !lean_is_exclusive(x_318);
if (x_388 == 0)
{
x_382 = x_318;
x_383 = x_388;
goto block_387;
}
else
{
lean_inc(x_381);
lean_dec(x_318);
x_382 = lean_box(0);
x_383 = x_388;
goto block_387;
}
block_387:
{
lean_object* x_384; 
if (x_383 == 0)
{
x_384 = x_382;
goto block_385;
}
else
{
lean_object* x_386; 
x_386 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_386, 0, x_381);
x_384 = x_386;
goto block_385;
}
block_385:
{
return x_384;
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
lean_object* x_389; 
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_del_object(x_70);
x_389 = l_Lean_Meta_Structural_isInstNegInt___redArg(x_82, x_8);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; uint8_t x_418; 
x_390 = lean_ctor_get(x_389, 0);
x_418 = !lean_is_exclusive(x_389);
if (x_418 == 0)
{
x_391 = x_389;
x_392 = x_418;
goto block_417;
}
else
{
lean_inc(x_390);
lean_dec(x_389);
x_391 = lean_box(0);
x_392 = x_418;
goto block_417;
}
block_417:
{
uint8_t x_393; 
x_393 = lean_unbox(x_390);
lean_dec(x_390);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; 
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_394 = lean_box(0);
if (x_392 == 0)
{
lean_ctor_set(x_391, 0, x_394);
x_395 = x_391;
goto block_396;
}
else
{
lean_object* x_397; 
x_397 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_397, 0, x_394);
x_395 = x_397;
goto block_396;
}
block_396:
{
return x_395;
}
}
else
{
lean_object* x_398; 
lean_del_object(x_391);
x_398 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
if (lean_obj_tag(x_399) == 0)
{
return x_398;
}
else
{
lean_object* x_400; uint8_t x_401; uint8_t x_415; 
x_415 = !lean_is_exclusive(x_398);
if (x_415 == 0)
{
lean_object* x_416; 
x_416 = lean_ctor_get(x_398, 0);
lean_dec(x_416);
x_400 = x_398;
x_401 = x_415;
goto block_414;
}
else
{
lean_dec(x_398);
x_400 = lean_box(0);
x_401 = x_415;
goto block_414;
}
block_414:
{
lean_object* x_402; lean_object* x_403; uint8_t x_404; uint8_t x_413; 
x_402 = lean_ctor_get(x_399, 0);
x_413 = !lean_is_exclusive(x_399);
if (x_413 == 0)
{
x_403 = x_399;
x_404 = x_413;
goto block_412;
}
else
{
lean_inc(x_402);
lean_dec(x_399);
x_403 = lean_box(0);
x_404 = x_413;
goto block_412;
}
block_412:
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_int_neg(x_402);
lean_dec(x_402);
if (x_404 == 0)
{
lean_ctor_set(x_403, 0, x_405);
x_406 = x_403;
goto block_410;
}
else
{
lean_object* x_411; 
x_411 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_411, 0, x_405);
x_406 = x_411;
goto block_410;
}
block_410:
{
lean_object* x_407; 
if (x_401 == 0)
{
lean_ctor_set(x_400, 0, x_406);
x_407 = x_400;
goto block_408;
}
else
{
lean_object* x_409; 
x_409 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_409, 0, x_406);
x_407 = x_409;
goto block_408;
}
block_408:
{
return x_407;
}
}
}
}
}
}
else
{
return x_398;
}
}
}
}
else
{
lean_object* x_419; lean_object* x_420; uint8_t x_421; uint8_t x_426; 
lean_dec_ref(x_79);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_419 = lean_ctor_get(x_389, 0);
x_426 = !lean_is_exclusive(x_389);
if (x_426 == 0)
{
x_420 = x_389;
x_421 = x_426;
goto block_425;
}
else
{
lean_inc(x_419);
lean_dec(x_389);
x_420 = lean_box(0);
x_421 = x_426;
goto block_425;
}
block_425:
{
lean_object* x_422; 
if (x_421 == 0)
{
x_422 = x_420;
goto block_423;
}
else
{
lean_object* x_424; 
x_424 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_424, 0, x_419);
x_422 = x_424;
goto block_423;
}
block_423:
{
return x_422;
}
}
}
}
}
else
{
lean_object* x_427; 
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec_ref(x_82);
lean_dec_ref(x_79);
lean_del_object(x_70);
x_427 = l_Lean_Meta_getIntValue_x3f(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_obj_tag(x_428) == 1)
{
lean_dec_ref(x_428);
return x_427;
}
else
{
lean_object* x_429; uint8_t x_430; uint8_t x_436; 
lean_dec(x_428);
x_436 = !lean_is_exclusive(x_427);
if (x_436 == 0)
{
lean_object* x_437; 
x_437 = lean_ctor_get(x_427, 0);
lean_dec(x_437);
x_429 = x_427;
x_430 = x_436;
goto block_435;
}
else
{
lean_dec(x_427);
x_429 = lean_box(0);
x_430 = x_436;
goto block_435;
}
block_435:
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_box(0);
if (x_430 == 0)
{
lean_ctor_set(x_429, 0, x_431);
x_432 = x_429;
goto block_433;
}
else
{
lean_object* x_434; 
x_434 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_434, 0, x_431);
x_432 = x_434;
goto block_433;
}
block_433:
{
return x_432;
}
}
}
}
else
{
return x_427;
}
}
}
else
{
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_del_object(x_70);
lean_dec_ref(x_1);
x_16 = x_82;
x_17 = x_79;
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
x_27 = lean_box(0);
goto block_67;
}
}
else
{
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_del_object(x_70);
lean_dec_ref(x_1);
x_16 = x_82;
x_17 = x_79;
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
x_27 = lean_box(0);
goto block_67;
}
}
}
}
block_76:
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_box(0);
if (x_71 == 0)
{
lean_ctor_set(x_70, 0, x_72);
x_73 = x_70;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
else
{
lean_object* x_440; lean_object* x_441; uint8_t x_442; uint8_t x_447; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_440 = lean_ctor_get(x_68, 0);
x_447 = !lean_is_exclusive(x_68);
if (x_447 == 0)
{
x_441 = x_68;
x_442 = x_447;
goto block_446;
}
else
{
lean_inc(x_440);
lean_dec(x_68);
x_441 = lean_box(0);
x_442 = x_447;
goto block_446;
}
block_446:
{
lean_object* x_443; 
if (x_442 == 0)
{
x_443 = x_441;
goto block_444;
}
else
{
lean_object* x_445; 
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_440);
x_443 = x_445;
goto block_444;
}
block_444:
{
return x_443;
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_67:
{
lean_object* x_28; 
x_28 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_16, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Expr_cleanupAnnotations(x_29);
x_31 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1));
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
lean_dec_ref(x_30);
if (x_32 == 0)
{
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_17);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_33; 
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_50; 
x_34 = lean_ctor_get(x_33, 0);
x_50 = !lean_is_exclusive(x_33);
if (x_50 == 0)
{
x_35 = x_33;
x_36 = x_50;
goto block_49;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_50;
goto block_49;
}
block_49:
{
if (lean_obj_tag(x_34) == 0)
{
lean_del_object(x_35);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_48; 
x_37 = lean_ctor_get(x_34, 0);
x_48 = !lean_is_exclusive(x_34);
if (x_48 == 0)
{
x_38 = x_34;
x_39 = x_48;
goto block_47;
}
else
{
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_box(0);
x_39 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_nat_to_int(x_37);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_40);
x_41 = x_38;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_40);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_41);
x_42 = x_35;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
x_51 = lean_ctor_get(x_33, 0);
x_58 = !lean_is_exclusive(x_33);
if (x_58 == 0)
{
x_52 = x_33;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_33);
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
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_17);
x_59 = lean_ctor_get(x_28, 0);
x_66 = !lean_is_exclusive(x_28);
if (x_66 == 0)
{
x_60 = x_28;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_28);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_418; 
x_17 = lean_ctor_get(x_16, 0);
x_418 = !lean_is_exclusive(x_16);
if (x_418 == 0)
{
x_18 = x_16;
x_19 = x_418;
goto block_417;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_418;
goto block_417;
}
block_417:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_Expr_cleanupAnnotations(x_17);
x_21 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2));
x_22 = l_Lean_Expr_isConstOf(x_20, x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_del_object(x_18);
x_23 = l_Lean_Expr_isApp(x_20);
if (x_23 == 0)
{
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_26 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5));
x_27 = l_Lean_Expr_isConstOf(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7));
x_29 = l_Lean_Expr_isConstOf(x_25, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9));
x_31 = l_Lean_Expr_isConstOf(x_25, x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_Expr_isApp(x_25);
if (x_32 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_33);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_36);
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_38 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12));
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec_ref(x_1);
x_40 = l_Lean_Expr_isApp(x_37);
if (x_40 == 0)
{
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Expr_appFnCleanup___redArg(x_37);
x_42 = l_Lean_Expr_isApp(x_41);
if (x_42 == 0)
{
lean_dec_ref(x_41);
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Expr_appFnCleanup___redArg(x_41);
x_44 = l_Lean_Expr_isApp(x_43);
if (x_44 == 0)
{
lean_dec_ref(x_43);
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Lean_Expr_appFnCleanup___redArg(x_43);
x_46 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15));
x_47 = l_Lean_Expr_isConstOf(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18));
x_49 = l_Lean_Expr_isConstOf(x_45, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21));
x_51 = l_Lean_Expr_isConstOf(x_45, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24));
x_53 = l_Lean_Expr_isConstOf(x_45, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27));
x_55 = l_Lean_Expr_isConstOf(x_45, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30));
x_57 = l_Lean_Expr_isConstOf(x_45, x_56);
lean_dec_ref(x_45);
if (x_57 == 0)
{
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_58; 
x_58 = l_Lean_Meta_Structural_isInstHAddNat___redArg(x_36, x_8);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_90; 
x_59 = lean_ctor_get(x_58, 0);
x_90 = !lean_is_exclusive(x_58);
if (x_90 == 0)
{
x_60 = x_58;
x_61 = x_90;
goto block_89;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_90;
goto block_89;
}
block_89:
{
uint8_t x_62; 
x_62 = lean_unbox(x_59);
lean_dec(x_59);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_63 = lean_box(0);
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_63);
x_64 = x_60;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_63);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
else
{
lean_object* x_67; 
lean_del_object(x_60);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_67;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_dec(x_69);
return x_70;
}
else
{
lean_object* x_72; uint8_t x_73; uint8_t x_87; 
x_87 = !lean_is_exclusive(x_70);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_70, 0);
lean_dec(x_88);
x_72 = x_70;
x_73 = x_87;
goto block_86;
}
else
{
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_85; 
x_74 = lean_ctor_get(x_71, 0);
x_85 = !lean_is_exclusive(x_71);
if (x_85 == 0)
{
x_75 = x_71;
x_76 = x_85;
goto block_84;
}
else
{
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_box(0);
x_76 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_nat_add(x_69, x_74);
lean_dec(x_74);
lean_dec(x_69);
if (x_76 == 0)
{
lean_ctor_set(x_75, 0, x_77);
x_78 = x_75;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_77);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_73 == 0)
{
lean_ctor_set(x_72, 0, x_78);
x_79 = x_72;
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
}
}
}
}
else
{
lean_dec(x_69);
return x_70;
}
}
}
else
{
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_67;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_98; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_91 = lean_ctor_get(x_58, 0);
x_98 = !lean_is_exclusive(x_58);
if (x_98 == 0)
{
x_92 = x_58;
x_93 = x_98;
goto block_97;
}
else
{
lean_inc(x_91);
lean_dec(x_58);
x_92 = lean_box(0);
x_93 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_94; 
if (x_93 == 0)
{
x_94 = x_92;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
}
}
else
{
lean_object* x_99; 
lean_dec_ref(x_45);
x_99 = l_Lean_Meta_Structural_isInstHMulNat___redArg(x_36, x_8);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_131; 
x_100 = lean_ctor_get(x_99, 0);
x_131 = !lean_is_exclusive(x_99);
if (x_131 == 0)
{
x_101 = x_99;
x_102 = x_131;
goto block_130;
}
else
{
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_box(0);
x_102 = x_131;
goto block_130;
}
block_130:
{
uint8_t x_103; 
x_103 = lean_unbox(x_100);
lean_dec(x_100);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_104 = lean_box(0);
if (x_102 == 0)
{
lean_ctor_set(x_101, 0, x_104);
x_105 = x_101;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_104);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
else
{
lean_object* x_108; 
lean_del_object(x_101);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_108 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_108;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec_ref(x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_dec(x_110);
return x_111;
}
else
{
lean_object* x_113; uint8_t x_114; uint8_t x_128; 
x_128 = !lean_is_exclusive(x_111);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_111, 0);
lean_dec(x_129);
x_113 = x_111;
x_114 = x_128;
goto block_127;
}
else
{
lean_dec(x_111);
x_113 = lean_box(0);
x_114 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_126; 
x_115 = lean_ctor_get(x_112, 0);
x_126 = !lean_is_exclusive(x_112);
if (x_126 == 0)
{
x_116 = x_112;
x_117 = x_126;
goto block_125;
}
else
{
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_box(0);
x_117 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_nat_mul(x_110, x_115);
lean_dec(x_115);
lean_dec(x_110);
if (x_117 == 0)
{
lean_ctor_set(x_116, 0, x_118);
x_119 = x_116;
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
if (x_114 == 0)
{
lean_ctor_set(x_113, 0, x_119);
x_120 = x_113;
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
}
else
{
lean_dec(x_110);
return x_111;
}
}
}
else
{
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_108;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_139; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_132 = lean_ctor_get(x_99, 0);
x_139 = !lean_is_exclusive(x_99);
if (x_139 == 0)
{
x_133 = x_99;
x_134 = x_139;
goto block_138;
}
else
{
lean_inc(x_132);
lean_dec(x_99);
x_133 = lean_box(0);
x_134 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_135; 
if (x_134 == 0)
{
x_135 = x_133;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_132);
x_135 = x_137;
goto block_136;
}
block_136:
{
return x_135;
}
}
}
}
}
else
{
lean_object* x_140; 
lean_dec_ref(x_45);
x_140 = l_Lean_Meta_Structural_isInstHSubNat___redArg(x_36, x_8);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_172; 
x_141 = lean_ctor_get(x_140, 0);
x_172 = !lean_is_exclusive(x_140);
if (x_172 == 0)
{
x_142 = x_140;
x_143 = x_172;
goto block_171;
}
else
{
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_box(0);
x_143 = x_172;
goto block_171;
}
block_171:
{
uint8_t x_144; 
x_144 = lean_unbox(x_141);
lean_dec(x_141);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_145 = lean_box(0);
if (x_143 == 0)
{
lean_ctor_set(x_142, 0, x_145);
x_146 = x_142;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_145);
x_146 = x_148;
goto block_147;
}
block_147:
{
return x_146;
}
}
else
{
lean_object* x_149; 
lean_del_object(x_142);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_149 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_149;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec_ref(x_149);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_dec(x_151);
return x_152;
}
else
{
lean_object* x_154; uint8_t x_155; uint8_t x_169; 
x_169 = !lean_is_exclusive(x_152);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_152, 0);
lean_dec(x_170);
x_154 = x_152;
x_155 = x_169;
goto block_168;
}
else
{
lean_dec(x_152);
x_154 = lean_box(0);
x_155 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_167; 
x_156 = lean_ctor_get(x_153, 0);
x_167 = !lean_is_exclusive(x_153);
if (x_167 == 0)
{
x_157 = x_153;
x_158 = x_167;
goto block_166;
}
else
{
lean_inc(x_156);
lean_dec(x_153);
x_157 = lean_box(0);
x_158 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_nat_sub(x_151, x_156);
lean_dec(x_156);
lean_dec(x_151);
if (x_158 == 0)
{
lean_ctor_set(x_157, 0, x_159);
x_160 = x_157;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_159);
x_160 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_161; 
if (x_155 == 0)
{
lean_ctor_set(x_154, 0, x_160);
x_161 = x_154;
goto block_162;
}
else
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_160);
x_161 = x_163;
goto block_162;
}
block_162:
{
return x_161;
}
}
}
}
}
}
else
{
lean_dec(x_151);
return x_152;
}
}
}
else
{
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_149;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_180; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_173 = lean_ctor_get(x_140, 0);
x_180 = !lean_is_exclusive(x_140);
if (x_180 == 0)
{
x_174 = x_140;
x_175 = x_180;
goto block_179;
}
else
{
lean_inc(x_173);
lean_dec(x_140);
x_174 = lean_box(0);
x_175 = x_180;
goto block_179;
}
block_179:
{
lean_object* x_176; 
if (x_175 == 0)
{
x_176 = x_174;
goto block_177;
}
else
{
lean_object* x_178; 
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_173);
x_176 = x_178;
goto block_177;
}
block_177:
{
return x_176;
}
}
}
}
}
else
{
lean_object* x_181; 
lean_dec_ref(x_45);
x_181 = l_Lean_Meta_Structural_isInstHDivNat___redArg(x_36, x_8);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_213; 
x_182 = lean_ctor_get(x_181, 0);
x_213 = !lean_is_exclusive(x_181);
if (x_213 == 0)
{
x_183 = x_181;
x_184 = x_213;
goto block_212;
}
else
{
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_box(0);
x_184 = x_213;
goto block_212;
}
block_212:
{
uint8_t x_185; 
x_185 = lean_unbox(x_182);
lean_dec(x_182);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_186 = lean_box(0);
if (x_184 == 0)
{
lean_ctor_set(x_183, 0, x_186);
x_187 = x_183;
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
else
{
lean_object* x_190; 
lean_del_object(x_183);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_190 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_190;
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec_ref(x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
x_193 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_dec(x_192);
return x_193;
}
else
{
lean_object* x_195; uint8_t x_196; uint8_t x_210; 
x_210 = !lean_is_exclusive(x_193);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_193, 0);
lean_dec(x_211);
x_195 = x_193;
x_196 = x_210;
goto block_209;
}
else
{
lean_dec(x_193);
x_195 = lean_box(0);
x_196 = x_210;
goto block_209;
}
block_209:
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_208; 
x_197 = lean_ctor_get(x_194, 0);
x_208 = !lean_is_exclusive(x_194);
if (x_208 == 0)
{
x_198 = x_194;
x_199 = x_208;
goto block_207;
}
else
{
lean_inc(x_197);
lean_dec(x_194);
x_198 = lean_box(0);
x_199 = x_208;
goto block_207;
}
block_207:
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_nat_div(x_192, x_197);
lean_dec(x_197);
lean_dec(x_192);
if (x_199 == 0)
{
lean_ctor_set(x_198, 0, x_200);
x_201 = x_198;
goto block_205;
}
else
{
lean_object* x_206; 
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_200);
x_201 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_202; 
if (x_196 == 0)
{
lean_ctor_set(x_195, 0, x_201);
x_202 = x_195;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_201);
x_202 = x_204;
goto block_203;
}
block_203:
{
return x_202;
}
}
}
}
}
}
else
{
lean_dec(x_192);
return x_193;
}
}
}
else
{
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_190;
}
}
}
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_221; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_214 = lean_ctor_get(x_181, 0);
x_221 = !lean_is_exclusive(x_181);
if (x_221 == 0)
{
x_215 = x_181;
x_216 = x_221;
goto block_220;
}
else
{
lean_inc(x_214);
lean_dec(x_181);
x_215 = lean_box(0);
x_216 = x_221;
goto block_220;
}
block_220:
{
lean_object* x_217; 
if (x_216 == 0)
{
x_217 = x_215;
goto block_218;
}
else
{
lean_object* x_219; 
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_214);
x_217 = x_219;
goto block_218;
}
block_218:
{
return x_217;
}
}
}
}
}
else
{
lean_object* x_222; 
lean_dec_ref(x_45);
x_222 = l_Lean_Meta_Structural_isInstHModNat___redArg(x_36, x_8);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; uint8_t x_254; 
x_223 = lean_ctor_get(x_222, 0);
x_254 = !lean_is_exclusive(x_222);
if (x_254 == 0)
{
x_224 = x_222;
x_225 = x_254;
goto block_253;
}
else
{
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_box(0);
x_225 = x_254;
goto block_253;
}
block_253:
{
uint8_t x_226; 
x_226 = lean_unbox(x_223);
lean_dec(x_223);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_227 = lean_box(0);
if (x_225 == 0)
{
lean_ctor_set(x_224, 0, x_227);
x_228 = x_224;
goto block_229;
}
else
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_227);
x_228 = x_230;
goto block_229;
}
block_229:
{
return x_228;
}
}
else
{
lean_object* x_231; 
lean_del_object(x_224);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_231 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_obj_tag(x_232) == 0)
{
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_231;
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec_ref(x_231);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_234 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
if (lean_obj_tag(x_235) == 0)
{
lean_dec(x_233);
return x_234;
}
else
{
lean_object* x_236; uint8_t x_237; uint8_t x_251; 
x_251 = !lean_is_exclusive(x_234);
if (x_251 == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_234, 0);
lean_dec(x_252);
x_236 = x_234;
x_237 = x_251;
goto block_250;
}
else
{
lean_dec(x_234);
x_236 = lean_box(0);
x_237 = x_251;
goto block_250;
}
block_250:
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_249; 
x_238 = lean_ctor_get(x_235, 0);
x_249 = !lean_is_exclusive(x_235);
if (x_249 == 0)
{
x_239 = x_235;
x_240 = x_249;
goto block_248;
}
else
{
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_box(0);
x_240 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_nat_mod(x_233, x_238);
lean_dec(x_238);
lean_dec(x_233);
if (x_240 == 0)
{
lean_ctor_set(x_239, 0, x_241);
x_242 = x_239;
goto block_246;
}
else
{
lean_object* x_247; 
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_241);
x_242 = x_247;
goto block_246;
}
block_246:
{
lean_object* x_243; 
if (x_237 == 0)
{
lean_ctor_set(x_236, 0, x_242);
x_243 = x_236;
goto block_244;
}
else
{
lean_object* x_245; 
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_242);
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
}
else
{
lean_dec(x_233);
return x_234;
}
}
}
else
{
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_231;
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_262; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_255 = lean_ctor_get(x_222, 0);
x_262 = !lean_is_exclusive(x_222);
if (x_262 == 0)
{
x_256 = x_222;
x_257 = x_262;
goto block_261;
}
else
{
lean_inc(x_255);
lean_dec(x_222);
x_256 = lean_box(0);
x_257 = x_262;
goto block_261;
}
block_261:
{
lean_object* x_258; 
if (x_257 == 0)
{
x_258 = x_256;
goto block_259;
}
else
{
lean_object* x_260; 
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_255);
x_258 = x_260;
goto block_259;
}
block_259:
{
return x_258;
}
}
}
}
}
else
{
lean_object* x_263; 
lean_dec_ref(x_45);
x_263 = l_Lean_Meta_Structural_isInstHPowNat___redArg(x_36, x_8);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_313; 
x_264 = lean_ctor_get(x_263, 0);
x_313 = !lean_is_exclusive(x_263);
if (x_313 == 0)
{
x_265 = x_263;
x_266 = x_313;
goto block_312;
}
else
{
lean_inc(x_264);
lean_dec(x_263);
x_265 = lean_box(0);
x_266 = x_313;
goto block_312;
}
block_312:
{
uint8_t x_267; 
x_267 = lean_unbox(x_264);
lean_dec(x_264);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_268 = lean_box(0);
if (x_266 == 0)
{
lean_ctor_set(x_265, 0, x_268);
x_269 = x_265;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_268);
x_269 = x_271;
goto block_270;
}
block_270:
{
return x_269;
}
}
else
{
lean_object* x_272; 
lean_del_object(x_265);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_272 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_dec_ref(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_272;
}
else
{
lean_object* x_274; lean_object* x_275; 
lean_dec_ref(x_272);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
lean_dec_ref(x_273);
lean_inc(x_274);
x_275 = l_Lean_Meta_Grind_Arith_checkExp(x_274, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_303; 
x_276 = lean_ctor_get(x_275, 0);
x_303 = !lean_is_exclusive(x_275);
if (x_303 == 0)
{
x_277 = x_275;
x_278 = x_303;
goto block_302;
}
else
{
lean_inc(x_276);
lean_dec(x_275);
x_277 = lean_box(0);
x_278 = x_303;
goto block_302;
}
block_302:
{
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_274);
lean_dec_ref(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_279 = lean_box(0);
if (x_278 == 0)
{
lean_ctor_set(x_277, 0, x_279);
x_280 = x_277;
goto block_281;
}
else
{
lean_object* x_282; 
x_282 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_282, 0, x_279);
x_280 = x_282;
goto block_281;
}
block_281:
{
return x_280;
}
}
else
{
lean_object* x_283; 
lean_dec_ref(x_276);
lean_del_object(x_277);
x_283 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
lean_dec(x_274);
return x_283;
}
else
{
lean_object* x_285; uint8_t x_286; uint8_t x_300; 
x_300 = !lean_is_exclusive(x_283);
if (x_300 == 0)
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_283, 0);
lean_dec(x_301);
x_285 = x_283;
x_286 = x_300;
goto block_299;
}
else
{
lean_dec(x_283);
x_285 = lean_box(0);
x_286 = x_300;
goto block_299;
}
block_299:
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_298; 
x_287 = lean_ctor_get(x_284, 0);
x_298 = !lean_is_exclusive(x_284);
if (x_298 == 0)
{
x_288 = x_284;
x_289 = x_298;
goto block_297;
}
else
{
lean_inc(x_287);
lean_dec(x_284);
x_288 = lean_box(0);
x_289 = x_298;
goto block_297;
}
block_297:
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_nat_pow(x_287, x_274);
lean_dec(x_274);
lean_dec(x_287);
if (x_289 == 0)
{
lean_ctor_set(x_288, 0, x_290);
x_291 = x_288;
goto block_295;
}
else
{
lean_object* x_296; 
x_296 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_296, 0, x_290);
x_291 = x_296;
goto block_295;
}
block_295:
{
lean_object* x_292; 
if (x_286 == 0)
{
lean_ctor_set(x_285, 0, x_291);
x_292 = x_285;
goto block_293;
}
else
{
lean_object* x_294; 
x_294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_294, 0, x_291);
x_292 = x_294;
goto block_293;
}
block_293:
{
return x_292;
}
}
}
}
}
}
else
{
lean_dec(x_274);
return x_283;
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; uint8_t x_311; 
lean_dec(x_274);
lean_dec_ref(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_304 = lean_ctor_get(x_275, 0);
x_311 = !lean_is_exclusive(x_275);
if (x_311 == 0)
{
x_305 = x_275;
x_306 = x_311;
goto block_310;
}
else
{
lean_inc(x_304);
lean_dec(x_275);
x_305 = lean_box(0);
x_306 = x_311;
goto block_310;
}
block_310:
{
lean_object* x_307; 
if (x_306 == 0)
{
x_307 = x_305;
goto block_308;
}
else
{
lean_object* x_309; 
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_304);
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
}
else
{
lean_dec_ref(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_272;
}
}
}
}
else
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; uint8_t x_321; 
lean_dec_ref(x_33);
lean_dec_ref(x_24);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_314 = lean_ctor_get(x_263, 0);
x_321 = !lean_is_exclusive(x_263);
if (x_321 == 0)
{
x_315 = x_263;
x_316 = x_321;
goto block_320;
}
else
{
lean_inc(x_314);
lean_dec(x_263);
x_315 = lean_box(0);
x_316 = x_321;
goto block_320;
}
block_320:
{
lean_object* x_317; 
if (x_316 == 0)
{
x_317 = x_315;
goto block_318;
}
else
{
lean_object* x_319; 
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_314);
x_317 = x_319;
goto block_318;
}
block_318:
{
return x_317;
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
lean_object* x_322; 
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec_ref(x_24);
x_322 = l_Lean_Meta_getNatValue_x3f(x_1, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
if (lean_obj_tag(x_323) == 1)
{
lean_dec_ref(x_323);
return x_322;
}
else
{
lean_object* x_324; uint8_t x_325; uint8_t x_331; 
lean_dec(x_323);
x_331 = !lean_is_exclusive(x_322);
if (x_331 == 0)
{
lean_object* x_332; 
x_332 = lean_ctor_get(x_322, 0);
lean_dec(x_332);
x_324 = x_322;
x_325 = x_331;
goto block_330;
}
else
{
lean_dec(x_322);
x_324 = lean_box(0);
x_325 = x_331;
goto block_330;
}
block_330:
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_box(0);
if (x_325 == 0)
{
lean_ctor_set(x_324, 0, x_326);
x_327 = x_324;
goto block_328;
}
else
{
lean_object* x_329; 
x_329 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_329, 0, x_326);
x_327 = x_329;
goto block_328;
}
block_328:
{
return x_327;
}
}
}
}
else
{
return x_322;
}
}
}
}
}
else
{
lean_object* x_333; 
lean_dec_ref(x_25);
lean_dec_ref(x_1);
x_333 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
if (lean_obj_tag(x_334) == 0)
{
return x_333;
}
else
{
lean_object* x_335; uint8_t x_336; uint8_t x_351; 
x_351 = !lean_is_exclusive(x_333);
if (x_351 == 0)
{
lean_object* x_352; 
x_352 = lean_ctor_get(x_333, 0);
lean_dec(x_352);
x_335 = x_333;
x_336 = x_351;
goto block_350;
}
else
{
lean_dec(x_333);
x_335 = lean_box(0);
x_336 = x_351;
goto block_350;
}
block_350:
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; uint8_t x_349; 
x_337 = lean_ctor_get(x_334, 0);
x_349 = !lean_is_exclusive(x_334);
if (x_349 == 0)
{
x_338 = x_334;
x_339 = x_349;
goto block_348;
}
else
{
lean_inc(x_337);
lean_dec(x_334);
x_338 = lean_box(0);
x_339 = x_349;
goto block_348;
}
block_348:
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_unsigned_to_nat(1u);
x_341 = lean_nat_add(x_337, x_340);
lean_dec(x_337);
if (x_339 == 0)
{
lean_ctor_set(x_338, 0, x_341);
x_342 = x_338;
goto block_346;
}
else
{
lean_object* x_347; 
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_341);
x_342 = x_347;
goto block_346;
}
block_346:
{
lean_object* x_343; 
if (x_336 == 0)
{
lean_ctor_set(x_335, 0, x_342);
x_343 = x_335;
goto block_344;
}
else
{
lean_object* x_345; 
x_345 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_345, 0, x_342);
x_343 = x_345;
goto block_344;
}
block_344:
{
return x_343;
}
}
}
}
}
}
else
{
return x_333;
}
}
}
else
{
lean_object* x_353; 
lean_dec_ref(x_25);
lean_dec_ref(x_1);
x_353 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; uint8_t x_374; 
x_354 = lean_ctor_get(x_353, 0);
x_374 = !lean_is_exclusive(x_353);
if (x_374 == 0)
{
x_355 = x_353;
x_356 = x_374;
goto block_373;
}
else
{
lean_inc(x_354);
lean_dec(x_353);
x_355 = lean_box(0);
x_356 = x_374;
goto block_373;
}
block_373:
{
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_box(0);
if (x_356 == 0)
{
lean_ctor_set(x_355, 0, x_357);
x_358 = x_355;
goto block_359;
}
else
{
lean_object* x_360; 
x_360 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_360, 0, x_357);
x_358 = x_360;
goto block_359;
}
block_359:
{
return x_358;
}
}
else
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; uint8_t x_372; 
x_361 = lean_ctor_get(x_354, 0);
x_372 = !lean_is_exclusive(x_354);
if (x_372 == 0)
{
x_362 = x_354;
x_363 = x_372;
goto block_371;
}
else
{
lean_inc(x_361);
lean_dec(x_354);
x_362 = lean_box(0);
x_363 = x_372;
goto block_371;
}
block_371:
{
lean_object* x_364; lean_object* x_365; 
x_364 = l_Int_toNat(x_361);
lean_dec(x_361);
if (x_363 == 0)
{
lean_ctor_set(x_362, 0, x_364);
x_365 = x_362;
goto block_369;
}
else
{
lean_object* x_370; 
x_370 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_370, 0, x_364);
x_365 = x_370;
goto block_369;
}
block_369:
{
lean_object* x_366; 
if (x_356 == 0)
{
lean_ctor_set(x_355, 0, x_365);
x_366 = x_355;
goto block_367;
}
else
{
lean_object* x_368; 
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_365);
x_366 = x_368;
goto block_367;
}
block_367:
{
return x_366;
}
}
}
}
}
}
else
{
lean_object* x_375; lean_object* x_376; uint8_t x_377; uint8_t x_382; 
x_375 = lean_ctor_get(x_353, 0);
x_382 = !lean_is_exclusive(x_353);
if (x_382 == 0)
{
x_376 = x_353;
x_377 = x_382;
goto block_381;
}
else
{
lean_inc(x_375);
lean_dec(x_353);
x_376 = lean_box(0);
x_377 = x_382;
goto block_381;
}
block_381:
{
lean_object* x_378; 
if (x_377 == 0)
{
x_378 = x_376;
goto block_379;
}
else
{
lean_object* x_380; 
x_380 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_380, 0, x_375);
x_378 = x_380;
goto block_379;
}
block_379:
{
return x_378;
}
}
}
}
}
else
{
lean_object* x_383; 
lean_dec_ref(x_25);
lean_dec_ref(x_1);
x_383 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; uint8_t x_386; uint8_t x_404; 
x_384 = lean_ctor_get(x_383, 0);
x_404 = !lean_is_exclusive(x_383);
if (x_404 == 0)
{
x_385 = x_383;
x_386 = x_404;
goto block_403;
}
else
{
lean_inc(x_384);
lean_dec(x_383);
x_385 = lean_box(0);
x_386 = x_404;
goto block_403;
}
block_403:
{
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_387; lean_object* x_388; 
x_387 = lean_box(0);
if (x_386 == 0)
{
lean_ctor_set(x_385, 0, x_387);
x_388 = x_385;
goto block_389;
}
else
{
lean_object* x_390; 
x_390 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_390, 0, x_387);
x_388 = x_390;
goto block_389;
}
block_389:
{
return x_388;
}
}
else
{
lean_object* x_391; lean_object* x_392; uint8_t x_393; uint8_t x_402; 
x_391 = lean_ctor_get(x_384, 0);
x_402 = !lean_is_exclusive(x_384);
if (x_402 == 0)
{
x_392 = x_384;
x_393 = x_402;
goto block_401;
}
else
{
lean_inc(x_391);
lean_dec(x_384);
x_392 = lean_box(0);
x_393 = x_402;
goto block_401;
}
block_401:
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_nat_abs(x_391);
lean_dec(x_391);
if (x_393 == 0)
{
lean_ctor_set(x_392, 0, x_394);
x_395 = x_392;
goto block_399;
}
else
{
lean_object* x_400; 
x_400 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_400, 0, x_394);
x_395 = x_400;
goto block_399;
}
block_399:
{
lean_object* x_396; 
if (x_386 == 0)
{
lean_ctor_set(x_385, 0, x_395);
x_396 = x_385;
goto block_397;
}
else
{
lean_object* x_398; 
x_398 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_398, 0, x_395);
x_396 = x_398;
goto block_397;
}
block_397:
{
return x_396;
}
}
}
}
}
}
else
{
lean_object* x_405; lean_object* x_406; uint8_t x_407; uint8_t x_412; 
x_405 = lean_ctor_get(x_383, 0);
x_412 = !lean_is_exclusive(x_383);
if (x_412 == 0)
{
x_406 = x_383;
x_407 = x_412;
goto block_411;
}
else
{
lean_inc(x_405);
lean_dec(x_383);
x_406 = lean_box(0);
x_407 = x_412;
goto block_411;
}
block_411:
{
lean_object* x_408; 
if (x_407 == 0)
{
x_408 = x_406;
goto block_409;
}
else
{
lean_object* x_410; 
x_410 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_410, 0, x_405);
x_408 = x_410;
goto block_409;
}
block_409:
{
return x_408;
}
}
}
}
}
}
else
{
lean_object* x_413; lean_object* x_414; 
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_413 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31));
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_413);
x_414 = x_18;
goto block_415;
}
else
{
lean_object* x_416; 
x_416 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_416, 0, x_413);
x_414 = x_416;
goto block_415;
}
block_415:
{
return x_414;
}
}
}
}
else
{
lean_object* x_419; lean_object* x_420; uint8_t x_421; uint8_t x_426; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_419 = lean_ctor_get(x_16, 0);
x_426 = !lean_is_exclusive(x_16);
if (x_426 == 0)
{
x_420 = x_16;
x_421 = x_426;
goto block_425;
}
else
{
lean_inc(x_419);
lean_dec(x_16);
x_420 = lean_box(0);
x_421 = x_426;
goto block_425;
}
block_425:
{
lean_object* x_422; 
if (x_421 == 0)
{
x_422 = x_420;
goto block_423;
}
else
{
lean_object* x_424; 
x_424 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_424, 0, x_419);
x_422 = x_424;
goto block_423;
}
block_423:
{
return x_422;
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_evalNat_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_evalInt_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
}
#ifdef __cplusplus
}
#endif
