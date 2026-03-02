// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.ControlFlow
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.ControlFlow import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.App import Lean.Meta.SynthInstance import Lean.Meta.WHNF import Lean.Meta.AppBuilder import Init.Sym.Lemmas import Lean.Meta.Tactic.Cbv.TheoremsLookup import Lean.Meta.Tactic.Cbv.Opaque
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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_false_of_decide"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(171, 157, 112, 124, 91, 52, 64, 56)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instDecidableFalse"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(49, 216, 212, 175, 154, 176, 165, 174)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ite_cond_congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(149, 115, 5, 135, 85, 70, 205, 95)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ite_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(217, 231, 214, 152, 207, 100, 121, 38)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_true_of_decide"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(10, 132, 193, 70, 136, 209, 66, 149)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instDecidableTrue"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(45, 239, 189, 64, 160, 216, 116, 23)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ite_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(28, 219, 17, 217, 43, 100, 109, 98)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "decidable_of_decidable_of_eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(124, 56, 184, 219, 10, 120, 143, 114)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ite_cond_eq_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(4, 35, 104, 204, 105, 138, 171, 217)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ite_cond_eq_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__31_value),LEAN_SCALAR_PTR_LITERAL(217, 214, 153, 207, 191, 74, 245, 103)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__32 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__32_value;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mpr_prop"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(169, 177, 76, 157, 211, 15, 217, 219)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7;
lean_object* l_Lean_mkBVar(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mpr_not"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(121, 56, 250, 51, 9, 123, 141, 181)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 21, 178, 198, 97, 164, 246, 137)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dite_cond_congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(72, 238, 116, 219, 106, 19, 52, 46)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dite_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(78, 119, 178, 178, 249, 126, 188, 7)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dite_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(65, 218, 189, 96, 14, 237, 238, 210)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dite_cond_eq_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__28_value),LEAN_SCALAR_PTR_LITERAL(153, 159, 146, 90, 178, 85, 98, 212)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "dite_cond_eq_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__30_value),LEAN_SCALAR_PTR_LITERAL(13, 104, 142, 126, 111, 138, 152, 2)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31_value;
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(lean_object*, lean_object*);
uint8_t l_Lean_instBEqReducibilityStatus_beq(uint8_t, uint8_t);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value;
lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0_value;
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 146, 92, 125, 27, 135, 153, 152)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_get(x_4);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_10 = x_4;
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_17; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
lean_inc(x_4);
lean_inc_ref(x_2);
x_18 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
x_10 = x_4;
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
x_20 = x_18;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
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
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_17, 0);
x_34 = !lean_is_exclusive(x_17);
if (x_34 == 0)
{
x_28 = x_17;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_app___override(x_1, x_2);
x_13 = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(x_12, x_10);
lean_dec(x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_14 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_15, x_3, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_15 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_16, x_4, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_16 = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1_spec__2(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_17, x_5, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__10));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__19));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__22));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__27));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_16; uint8_t x_17; 
lean_inc_ref(x_2);
x_16 = l_Lean_Expr_cleanupAnnotations(x_2);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
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
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__1));
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
if (x_33 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_34; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_27);
x_34 = lean_sym_simp(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; uint8_t x_257; 
x_257 = !lean_is_exclusive(x_35);
if (x_257 == 0)
{
x_36 = x_35;
x_37 = x_257;
goto block_256;
}
else
{
lean_dec(x_35);
x_36 = lean_box(0);
x_37 = x_257;
goto block_256;
}
block_256:
{
lean_object* x_38; 
x_38 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_247; 
x_39 = lean_ctor_get(x_38, 0);
x_247 = !lean_is_exclusive(x_38);
if (x_247 == 0)
{
x_40 = x_38;
x_41 = x_247;
goto block_246;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_247;
goto block_246;
}
block_246:
{
uint8_t x_42; 
x_42 = lean_unbox(x_39);
if (x_42 == 0)
{
lean_object* x_43; 
lean_del_object(x_40);
x_43 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_229; 
x_44 = lean_ctor_get(x_43, 0);
x_229 = !lean_is_exclusive(x_43);
if (x_229 == 0)
{
x_45 = x_43;
x_46 = x_229;
goto block_228;
}
else
{
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = x_229;
goto block_228;
}
block_228:
{
uint8_t x_47; 
x_47 = lean_unbox(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_del_object(x_45);
lean_dec(x_39);
x_48 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_49 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_48, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_51 = lean_sym_simp(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_210; 
x_52 = lean_ctor_get(x_51, 0);
x_210 = !lean_is_exclusive(x_51);
if (x_210 == 0)
{
x_53 = x_51;
x_54 = x_210;
goto block_209;
}
else
{
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = x_210;
goto block_209;
}
block_209:
{
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_55; uint8_t x_56; uint8_t x_64; 
lean_dec(x_44);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_64 = !lean_is_exclusive(x_52);
if (x_64 == 0)
{
x_55 = x_52;
x_56 = x_64;
goto block_63;
}
else
{
lean_dec(x_52);
x_55 = lean_box(0);
x_56 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 0, 1);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
lean_ctor_set_uint8(x_57, 0, x_33);
if (x_54 == 0)
{
lean_ctor_set(x_53, 0, x_57);
x_58 = x_53;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_208; 
lean_del_object(x_53);
x_65 = lean_ctor_get(x_52, 0);
x_66 = lean_ctor_get(x_52, 1);
x_208 = !lean_is_exclusive(x_52);
if (x_208 == 0)
{
x_67 = x_52;
x_68 = x_208;
goto block_207;
}
else
{
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_52);
x_67 = lean_box(0);
x_68 = x_208;
goto block_207;
}
block_207:
{
lean_object* x_69; 
x_69 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_65, x_6);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_unbox(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_44);
x_72 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_65, x_6);
lean_dec_ref(x_65);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_137; 
x_73 = lean_ctor_get(x_72, 0);
x_137 = !lean_is_exclusive(x_72);
if (x_137 == 0)
{
x_74 = x_72;
x_75 = x_137;
goto block_136;
}
else
{
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = x_137;
goto block_136;
}
block_136:
{
uint8_t x_76; 
x_76 = lean_unbox(x_73);
lean_dec(x_73);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_70);
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (x_37 == 0)
{
x_77 = x_36;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 0, 1);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
lean_ctor_set_uint8(x_77, 0, x_33);
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_77);
x_78 = x_74;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_77);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
else
{
lean_object* x_83; 
lean_del_object(x_74);
lean_del_object(x_36);
x_83 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
x_86 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_87 = lean_unsigned_to_nat(4u);
x_88 = l_Lean_Expr_getBoundedAppFn(x_87, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_84);
x_89 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_88, x_84, x_86, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_mkApp3(x_85, x_27, x_24, x_66);
x_92 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_93 = l_Lean_Expr_replaceFn(x_2, x_92);
x_94 = l_Lean_mkApp3(x_93, x_84, x_86, x_91);
x_95 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_96 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_97 = l_Lean_mkConst(x_95, x_96);
lean_inc_ref(x_18);
x_98 = l_Lean_mkApp3(x_97, x_30, x_21, x_18);
lean_inc_ref(x_18);
x_99 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_90, x_94, x_18, x_98, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_111; 
x_100 = lean_ctor_get(x_99, 0);
x_111 = !lean_is_exclusive(x_99);
if (x_111 == 0)
{
x_101 = x_99;
x_102 = x_111;
goto block_110;
}
else
{
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_box(0);
x_102 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_103; 
if (x_68 == 0)
{
lean_ctor_set(x_67, 1, x_100);
lean_ctor_set(x_67, 0, x_18);
x_103 = x_67;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_109, 0, x_18);
lean_ctor_set(x_109, 1, x_100);
x_103 = x_109;
goto block_108;
}
block_108:
{
uint8_t x_104; lean_object* x_105; 
x_104 = lean_unbox(x_70);
lean_dec(x_70);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_104);
if (x_102 == 0)
{
lean_ctor_set(x_101, 0, x_103);
x_105 = x_101;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_103);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
lean_dec(x_70);
lean_del_object(x_67);
lean_dec_ref(x_18);
x_112 = lean_ctor_get(x_99, 0);
x_119 = !lean_is_exclusive(x_99);
if (x_119 == 0)
{
x_113 = x_99;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_99);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_127; 
lean_dec(x_84);
lean_dec(x_70);
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_120 = lean_ctor_get(x_89, 0);
x_127 = !lean_is_exclusive(x_89);
if (x_127 == 0)
{
x_121 = x_89;
x_122 = x_127;
goto block_126;
}
else
{
lean_inc(x_120);
lean_dec(x_89);
x_121 = lean_box(0);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_122 == 0)
{
x_123 = x_121;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_135; 
lean_dec(x_70);
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_128 = lean_ctor_get(x_83, 0);
x_135 = !lean_is_exclusive(x_83);
if (x_135 == 0)
{
x_129 = x_83;
x_130 = x_135;
goto block_134;
}
else
{
lean_inc(x_128);
lean_dec(x_83);
x_129 = lean_box(0);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_130 == 0)
{
x_131 = x_129;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_128);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_145; 
lean_dec(x_70);
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_138 = lean_ctor_get(x_72, 0);
x_145 = !lean_is_exclusive(x_72);
if (x_145 == 0)
{
x_139 = x_72;
x_140 = x_145;
goto block_144;
}
else
{
lean_inc(x_138);
lean_dec(x_72);
x_139 = lean_box(0);
x_140 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_141; 
if (x_140 == 0)
{
x_141 = x_139;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_138);
x_141 = x_143;
goto block_142;
}
block_142:
{
return x_141;
}
}
}
}
else
{
lean_object* x_146; 
lean_dec(x_70);
lean_dec_ref(x_65);
lean_del_object(x_36);
x_146 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
x_149 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_150 = lean_unsigned_to_nat(4u);
x_151 = l_Lean_Expr_getBoundedAppFn(x_150, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_18);
lean_inc_ref(x_21);
lean_inc(x_147);
x_152 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_151, x_147, x_149, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = l_Lean_mkApp3(x_148, x_27, x_24, x_66);
x_155 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
lean_inc_ref(x_2);
x_156 = l_Lean_Expr_replaceFn(x_2, x_155);
x_157 = l_Lean_mkApp3(x_156, x_147, x_149, x_154);
x_158 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_159 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_160 = l_Lean_mkConst(x_158, x_159);
lean_inc_ref(x_21);
x_161 = l_Lean_mkApp3(x_160, x_30, x_21, x_18);
lean_inc_ref(x_21);
x_162 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_153, x_157, x_21, x_161, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_174; 
x_163 = lean_ctor_get(x_162, 0);
x_174 = !lean_is_exclusive(x_162);
if (x_174 == 0)
{
x_164 = x_162;
x_165 = x_174;
goto block_173;
}
else
{
lean_inc(x_163);
lean_dec(x_162);
x_164 = lean_box(0);
x_165 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_166; 
if (x_68 == 0)
{
lean_ctor_set(x_67, 1, x_163);
lean_ctor_set(x_67, 0, x_21);
x_166 = x_67;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_172, 0, x_21);
lean_ctor_set(x_172, 1, x_163);
x_166 = x_172;
goto block_171;
}
block_171:
{
uint8_t x_167; lean_object* x_168; 
x_167 = lean_unbox(x_44);
lean_dec(x_44);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_167);
if (x_165 == 0)
{
lean_ctor_set(x_164, 0, x_166);
x_168 = x_164;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_166);
x_168 = x_170;
goto block_169;
}
block_169:
{
return x_168;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_182; 
lean_del_object(x_67);
lean_dec(x_44);
lean_dec_ref(x_21);
x_175 = lean_ctor_get(x_162, 0);
x_182 = !lean_is_exclusive(x_162);
if (x_182 == 0)
{
x_176 = x_162;
x_177 = x_182;
goto block_181;
}
else
{
lean_inc(x_175);
lean_dec(x_162);
x_176 = lean_box(0);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_177 == 0)
{
x_178 = x_176;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_175);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_190; 
lean_dec(x_147);
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec(x_44);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_183 = lean_ctor_get(x_152, 0);
x_190 = !lean_is_exclusive(x_152);
if (x_190 == 0)
{
x_184 = x_152;
x_185 = x_190;
goto block_189;
}
else
{
lean_inc(x_183);
lean_dec(x_152);
x_184 = lean_box(0);
x_185 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_186; 
if (x_185 == 0)
{
x_186 = x_184;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_183);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_198; 
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec(x_44);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_191 = lean_ctor_get(x_146, 0);
x_198 = !lean_is_exclusive(x_146);
if (x_198 == 0)
{
x_192 = x_146;
x_193 = x_198;
goto block_197;
}
else
{
lean_inc(x_191);
lean_dec(x_146);
x_192 = lean_box(0);
x_193 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_194; 
if (x_193 == 0)
{
x_194 = x_192;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_191);
x_194 = x_196;
goto block_195;
}
block_195:
{
return x_194;
}
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_206; 
lean_del_object(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec(x_44);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_199 = lean_ctor_get(x_69, 0);
x_206 = !lean_is_exclusive(x_69);
if (x_206 == 0)
{
x_200 = x_69;
x_201 = x_206;
goto block_205;
}
else
{
lean_inc(x_199);
lean_dec(x_69);
x_200 = lean_box(0);
x_201 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_202; 
if (x_201 == 0)
{
x_202 = x_200;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_199);
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
}
else
{
lean_dec(x_44);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_51;
}
}
else
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_218; 
lean_dec(x_44);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_211 = lean_ctor_get(x_49, 0);
x_218 = !lean_is_exclusive(x_49);
if (x_218 == 0)
{
x_212 = x_49;
x_213 = x_218;
goto block_217;
}
else
{
lean_inc(x_211);
lean_dec(x_49);
x_212 = lean_box(0);
x_213 = x_218;
goto block_217;
}
block_217:
{
lean_object* x_214; 
if (x_213 == 0)
{
x_214 = x_212;
goto block_215;
}
else
{
lean_object* x_216; 
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_211);
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
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; 
lean_dec(x_44);
lean_del_object(x_36);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_219 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__17));
x_220 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_221 = l_Lean_mkConst(x_219, x_220);
lean_inc_ref(x_18);
x_222 = l_Lean_mkApp3(x_221, x_30, x_21, x_18);
x_223 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_223, 0, x_18);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_unbox(x_39);
lean_dec(x_39);
lean_ctor_set_uint8(x_223, sizeof(void*)*2, x_224);
if (x_46 == 0)
{
lean_ctor_set(x_45, 0, x_223);
x_225 = x_45;
goto block_226;
}
else
{
lean_object* x_227; 
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_223);
x_225 = x_227;
goto block_226;
}
block_226:
{
return x_225;
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_237; 
lean_dec(x_39);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_230 = lean_ctor_get(x_43, 0);
x_237 = !lean_is_exclusive(x_43);
if (x_237 == 0)
{
x_231 = x_43;
x_232 = x_237;
goto block_236;
}
else
{
lean_inc(x_230);
lean_dec(x_43);
x_231 = lean_box(0);
x_232 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_233; 
if (x_232 == 0)
{
x_233 = x_231;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_230);
x_233 = x_235;
goto block_234;
}
block_234:
{
return x_233;
}
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_39);
lean_del_object(x_36);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_238 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__25));
x_239 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_240 = l_Lean_mkConst(x_238, x_239);
lean_inc_ref(x_21);
x_241 = l_Lean_mkApp3(x_240, x_30, x_21, x_18);
x_242 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_242, 0, x_21);
lean_ctor_set(x_242, 1, x_241);
lean_ctor_set_uint8(x_242, sizeof(void*)*2, x_1);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_242);
x_243 = x_40;
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
else
{
lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_255; 
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_248 = lean_ctor_get(x_38, 0);
x_255 = !lean_is_exclusive(x_38);
if (x_255 == 0)
{
x_249 = x_38;
x_250 = x_255;
goto block_254;
}
else
{
lean_inc(x_248);
lean_dec(x_38);
x_249 = lean_box(0);
x_250 = x_255;
goto block_254;
}
block_254:
{
lean_object* x_251; 
if (x_250 == 0)
{
x_251 = x_249;
goto block_252;
}
else
{
lean_object* x_253; 
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_248);
x_251 = x_253;
goto block_252;
}
block_252:
{
return x_251;
}
}
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_340; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
x_258 = lean_ctor_get(x_35, 0);
x_259 = lean_ctor_get(x_35, 1);
x_340 = !lean_is_exclusive(x_35);
if (x_340 == 0)
{
x_260 = x_35;
x_261 = x_340;
goto block_339;
}
else
{
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_35);
x_260 = lean_box(0);
x_261 = x_340;
goto block_339;
}
block_339:
{
lean_object* x_262; 
x_262 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_258, x_6);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; uint8_t x_330; 
x_263 = lean_ctor_get(x_262, 0);
x_330 = !lean_is_exclusive(x_262);
if (x_330 == 0)
{
x_264 = x_262;
x_265 = x_330;
goto block_329;
}
else
{
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_box(0);
x_265 = x_330;
goto block_329;
}
block_329:
{
uint8_t x_266; 
x_266 = lean_unbox(x_263);
if (x_266 == 0)
{
lean_object* x_267; 
lean_del_object(x_264);
x_267 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_258, x_6);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; uint8_t x_311; 
x_268 = lean_ctor_get(x_267, 0);
x_311 = !lean_is_exclusive(x_267);
if (x_311 == 0)
{
x_269 = x_267;
x_270 = x_311;
goto block_310;
}
else
{
lean_inc(x_268);
lean_dec(x_267);
x_269 = lean_box(0);
x_270 = x_311;
goto block_310;
}
block_310:
{
uint8_t x_271; 
x_271 = lean_unbox(x_268);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_del_object(x_269);
lean_dec(x_263);
x_272 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28);
lean_inc_ref(x_259);
lean_inc_ref(x_258);
x_273 = l_Lean_mkApp4(x_272, x_27, x_258, x_24, x_259);
x_274 = lean_unsigned_to_nat(4u);
x_275 = l_Lean_Expr_getBoundedAppFn(x_274, x_2);
lean_inc_ref(x_273);
lean_inc_ref(x_258);
x_276 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_275, x_258, x_273, x_21, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; uint8_t x_291; 
x_277 = lean_ctor_get(x_276, 0);
x_291 = !lean_is_exclusive(x_276);
if (x_291 == 0)
{
x_278 = x_276;
x_279 = x_291;
goto block_290;
}
else
{
lean_inc(x_277);
lean_dec(x_276);
x_278 = lean_box(0);
x_279 = x_291;
goto block_290;
}
block_290:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_280 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__15));
x_281 = l_Lean_Expr_replaceFn(x_2, x_280);
x_282 = l_Lean_mkApp3(x_281, x_258, x_273, x_259);
if (x_261 == 0)
{
lean_ctor_set(x_260, 1, x_282);
lean_ctor_set(x_260, 0, x_277);
x_283 = x_260;
goto block_288;
}
else
{
lean_object* x_289; 
x_289 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_289, 0, x_277);
lean_ctor_set(x_289, 1, x_282);
x_283 = x_289;
goto block_288;
}
block_288:
{
uint8_t x_284; lean_object* x_285; 
x_284 = lean_unbox(x_268);
lean_dec(x_268);
lean_ctor_set_uint8(x_283, sizeof(void*)*2, x_284);
if (x_279 == 0)
{
lean_ctor_set(x_278, 0, x_283);
x_285 = x_278;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_283);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
}
else
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_299; 
lean_dec_ref(x_273);
lean_dec(x_268);
lean_del_object(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_2);
x_292 = lean_ctor_get(x_276, 0);
x_299 = !lean_is_exclusive(x_276);
if (x_299 == 0)
{
x_293 = x_276;
x_294 = x_299;
goto block_298;
}
else
{
lean_inc(x_292);
lean_dec(x_276);
x_293 = lean_box(0);
x_294 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_295; 
if (x_294 == 0)
{
x_295 = x_293;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_292);
x_295 = x_297;
goto block_296;
}
block_296:
{
return x_295;
}
}
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_268);
lean_dec_ref(x_258);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_300 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__30));
x_301 = l_Lean_Expr_replaceFn(x_2, x_300);
x_302 = l_Lean_Expr_app___override(x_301, x_259);
if (x_261 == 0)
{
lean_ctor_set(x_260, 1, x_302);
lean_ctor_set(x_260, 0, x_18);
x_303 = x_260;
goto block_308;
}
else
{
lean_object* x_309; 
x_309 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_309, 0, x_18);
lean_ctor_set(x_309, 1, x_302);
x_303 = x_309;
goto block_308;
}
block_308:
{
uint8_t x_304; lean_object* x_305; 
x_304 = lean_unbox(x_263);
lean_dec(x_263);
lean_ctor_set_uint8(x_303, sizeof(void*)*2, x_304);
if (x_270 == 0)
{
lean_ctor_set(x_269, 0, x_303);
x_305 = x_269;
goto block_306;
}
else
{
lean_object* x_307; 
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_303);
x_305 = x_307;
goto block_306;
}
block_306:
{
return x_305;
}
}
}
}
}
else
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; uint8_t x_319; 
lean_dec(x_263);
lean_del_object(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_312 = lean_ctor_get(x_267, 0);
x_319 = !lean_is_exclusive(x_267);
if (x_319 == 0)
{
x_313 = x_267;
x_314 = x_319;
goto block_318;
}
else
{
lean_inc(x_312);
lean_dec(x_267);
x_313 = lean_box(0);
x_314 = x_319;
goto block_318;
}
block_318:
{
lean_object* x_315; 
if (x_314 == 0)
{
x_315 = x_313;
goto block_316;
}
else
{
lean_object* x_317; 
x_317 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_317, 0, x_312);
x_315 = x_317;
goto block_316;
}
block_316:
{
return x_315;
}
}
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_263);
lean_dec_ref(x_258);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_320 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__32));
x_321 = l_Lean_Expr_replaceFn(x_2, x_320);
x_322 = l_Lean_Expr_app___override(x_321, x_259);
if (x_261 == 0)
{
lean_ctor_set(x_260, 1, x_322);
lean_ctor_set(x_260, 0, x_21);
x_323 = x_260;
goto block_327;
}
else
{
lean_object* x_328; 
x_328 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_328, 0, x_21);
lean_ctor_set(x_328, 1, x_322);
x_323 = x_328;
goto block_327;
}
block_327:
{
lean_object* x_324; 
lean_ctor_set_uint8(x_323, sizeof(void*)*2, x_1);
if (x_265 == 0)
{
lean_ctor_set(x_264, 0, x_323);
x_324 = x_264;
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
}
}
}
else
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; uint8_t x_338; 
lean_del_object(x_260);
lean_dec_ref(x_259);
lean_dec_ref(x_258);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_331 = lean_ctor_get(x_262, 0);
x_338 = !lean_is_exclusive(x_262);
if (x_338 == 0)
{
x_332 = x_262;
x_333 = x_338;
goto block_337;
}
else
{
lean_inc(x_331);
lean_dec(x_262);
x_332 = lean_box(0);
x_333 = x_338;
goto block_337;
}
block_337:
{
lean_object* x_334; 
if (x_333 == 0)
{
x_334 = x_332;
goto block_335;
}
else
{
lean_object* x_336; 
x_336 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_336, 0, x_331);
x_334 = x_336;
goto block_335;
}
block_335:
{
return x_334;
}
}
}
}
}
}
else
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_34;
}
}
}
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Expr_getAppNumArgs(x_1);
x_13 = lean_unsigned_to_nat(5u);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 12, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_18 = l_Lean_Meta_Sym_Simp_propagateOverApplied(x_1, x_17, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_19, 0, x_14);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Simp_simpIteCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkBVar(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15);
x_2 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__23));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__24);
x_2 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_16; uint8_t x_17; 
lean_inc_ref(x_2);
x_16 = l_Lean_Expr_cleanupAnnotations(x_2);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
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
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1));
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
if (x_33 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_34; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_27);
x_34 = lean_sym_simp(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; uint8_t x_409; 
x_409 = !lean_is_exclusive(x_35);
if (x_409 == 0)
{
x_36 = x_35;
x_37 = x_409;
goto block_408;
}
else
{
lean_dec(x_35);
x_36 = lean_box(0);
x_37 = x_409;
goto block_408;
}
block_408:
{
lean_object* x_38; 
x_38 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_unbox(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_27, x_6);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_39);
x_44 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_24);
lean_inc_ref(x_27);
x_45 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__0(x_44, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_47 = lean_sym_simp(x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_332; 
x_48 = lean_ctor_get(x_47, 0);
x_332 = !lean_is_exclusive(x_47);
if (x_332 == 0)
{
x_49 = x_47;
x_50 = x_332;
goto block_331;
}
else
{
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = x_332;
goto block_331;
}
block_331:
{
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_51; uint8_t x_52; uint8_t x_60; 
lean_dec(x_42);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
x_51 = x_48;
x_52 = x_60;
goto block_59;
}
else
{
lean_dec(x_48);
x_51 = lean_box(0);
x_52 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 0, 1);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
lean_ctor_set_uint8(x_53, 0, x_33);
if (x_50 == 0)
{
lean_ctor_set(x_49, 0, x_53);
x_54 = x_49;
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
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_330; 
lean_del_object(x_49);
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
x_330 = !lean_is_exclusive(x_48);
if (x_330 == 0)
{
x_63 = x_48;
x_64 = x_330;
goto block_329;
}
else
{
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_63 = lean_box(0);
x_64 = x_330;
goto block_329;
}
block_329:
{
lean_object* x_65; 
x_65 = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(x_61, x_6);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_unbox(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_42);
x_68 = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(x_61, x_6);
lean_dec_ref(x_61);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_196; 
x_69 = lean_ctor_get(x_68, 0);
x_196 = !lean_is_exclusive(x_68);
if (x_196 == 0)
{
x_70 = x_68;
x_71 = x_196;
goto block_195;
}
else
{
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
x_71 = x_196;
goto block_195;
}
block_195:
{
uint8_t x_72; 
x_72 = lean_unbox(x_69);
lean_dec(x_69);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (x_37 == 0)
{
x_73 = x_36;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 0, 1);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
lean_ctor_set_uint8(x_73, 0, x_33);
if (x_71 == 0)
{
lean_ctor_set(x_70, 0, x_73);
x_74 = x_70;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_del_object(x_70);
lean_del_object(x_36);
x_79 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__8);
lean_inc_ref(x_27);
x_80 = l_Lean_mkApp3(x_79, x_27, x_24, x_62);
x_81 = l_Lean_Meta_Sym_shareCommon___redArg(x_80, x_7);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = l_Lean_Meta_Sym_getFalseExpr___redArg(x_6);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__11);
x_86 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_87 = 0;
x_88 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_89 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_82);
lean_inc(x_84);
lean_inc_ref(x_27);
x_90 = l_Lean_mkApp4(x_88, x_27, x_84, x_82, x_89);
x_91 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_92 = lean_array_push(x_91, x_90);
x_93 = lean_unbox(x_66);
x_94 = lean_unbox(x_66);
x_95 = l_Lean_Expr_betaRev(x_21, x_92, x_93, x_94);
lean_dec_ref(x_92);
lean_inc(x_84);
x_96 = l_Lean_mkLambda(x_86, x_87, x_84, x_95);
x_97 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_96, x_7);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
lean_inc(x_84);
x_99 = l_Lean_mkNot(x_84);
x_100 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_82);
lean_inc(x_84);
x_101 = l_Lean_mkApp4(x_100, x_27, x_84, x_82, x_89);
x_102 = lean_array_push(x_91, x_101);
x_103 = lean_unbox(x_66);
x_104 = lean_unbox(x_66);
x_105 = l_Lean_Expr_betaRev(x_18, x_102, x_103, x_104);
lean_dec_ref(x_102);
x_106 = l_Lean_mkLambda(x_86, x_87, x_99, x_105);
x_107 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_106, x_7);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_unsigned_to_nat(4u);
x_110 = l_Lean_Expr_getBoundedAppFn(x_109, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_108);
lean_inc(x_98);
lean_inc(x_84);
x_111 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_110, x_84, x_85, x_98, x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16);
x_114 = lean_unbox(x_66);
x_115 = lean_unbox(x_66);
lean_inc(x_108);
x_116 = l_Lean_Expr_betaRev(x_108, x_113, x_114, x_115);
x_117 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_116, x_7);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_120 = l_Lean_Expr_replaceFn(x_2, x_119);
x_121 = l_Lean_mkApp3(x_120, x_84, x_85, x_82);
x_122 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_123 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_124 = l_Lean_mkConst(x_122, x_123);
x_125 = l_Lean_mkApp3(x_124, x_30, x_98, x_108);
lean_inc(x_118);
x_126 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_112, x_121, x_118, x_125, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_138; 
x_127 = lean_ctor_get(x_126, 0);
x_138 = !lean_is_exclusive(x_126);
if (x_138 == 0)
{
x_128 = x_126;
x_129 = x_138;
goto block_137;
}
else
{
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_box(0);
x_129 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_130; 
if (x_64 == 0)
{
lean_ctor_set(x_63, 1, x_127);
lean_ctor_set(x_63, 0, x_118);
x_130 = x_63;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_136, 0, x_118);
lean_ctor_set(x_136, 1, x_127);
x_130 = x_136;
goto block_135;
}
block_135:
{
uint8_t x_131; lean_object* x_132; 
x_131 = lean_unbox(x_66);
lean_dec(x_66);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_131);
if (x_129 == 0)
{
lean_ctor_set(x_128, 0, x_130);
x_132 = x_128;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_130);
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
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_146; 
lean_dec(x_118);
lean_dec(x_66);
lean_del_object(x_63);
x_139 = lean_ctor_get(x_126, 0);
x_146 = !lean_is_exclusive(x_126);
if (x_146 == 0)
{
x_140 = x_126;
x_141 = x_146;
goto block_145;
}
else
{
lean_inc(x_139);
lean_dec(x_126);
x_140 = lean_box(0);
x_141 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_142; 
if (x_141 == 0)
{
x_142 = x_140;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_139);
x_142 = x_144;
goto block_143;
}
block_143:
{
return x_142;
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_154; 
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_98);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_147 = lean_ctor_get(x_117, 0);
x_154 = !lean_is_exclusive(x_117);
if (x_154 == 0)
{
x_148 = x_117;
x_149 = x_154;
goto block_153;
}
else
{
lean_inc(x_147);
lean_dec(x_117);
x_148 = lean_box(0);
x_149 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_150; 
if (x_149 == 0)
{
x_150 = x_148;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_147);
x_150 = x_152;
goto block_151;
}
block_151:
{
return x_150;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_162; 
lean_dec(x_108);
lean_dec(x_98);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_155 = lean_ctor_get(x_111, 0);
x_162 = !lean_is_exclusive(x_111);
if (x_162 == 0)
{
x_156 = x_111;
x_157 = x_162;
goto block_161;
}
else
{
lean_inc(x_155);
lean_dec(x_111);
x_156 = lean_box(0);
x_157 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_158; 
if (x_157 == 0)
{
x_158 = x_156;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_155);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_170; 
lean_dec(x_98);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_163 = lean_ctor_get(x_107, 0);
x_170 = !lean_is_exclusive(x_107);
if (x_170 == 0)
{
x_164 = x_107;
x_165 = x_170;
goto block_169;
}
else
{
lean_inc(x_163);
lean_dec(x_107);
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
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_171 = lean_ctor_get(x_97, 0);
x_178 = !lean_is_exclusive(x_97);
if (x_178 == 0)
{
x_172 = x_97;
x_173 = x_178;
goto block_177;
}
else
{
lean_inc(x_171);
lean_dec(x_97);
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
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_186; 
lean_dec(x_82);
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_179 = lean_ctor_get(x_83, 0);
x_186 = !lean_is_exclusive(x_83);
if (x_186 == 0)
{
x_180 = x_83;
x_181 = x_186;
goto block_185;
}
else
{
lean_inc(x_179);
lean_dec(x_83);
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
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_187 = lean_ctor_get(x_81, 0);
x_194 = !lean_is_exclusive(x_81);
if (x_194 == 0)
{
x_188 = x_81;
x_189 = x_194;
goto block_193;
}
else
{
lean_inc(x_187);
lean_dec(x_81);
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
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_204; 
lean_dec(x_66);
lean_del_object(x_63);
lean_dec_ref(x_62);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_197 = lean_ctor_get(x_68, 0);
x_204 = !lean_is_exclusive(x_68);
if (x_204 == 0)
{
x_198 = x_68;
x_199 = x_204;
goto block_203;
}
else
{
lean_inc(x_197);
lean_dec(x_68);
x_198 = lean_box(0);
x_199 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_200; 
if (x_199 == 0)
{
x_200 = x_198;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_197);
x_200 = x_202;
goto block_201;
}
block_201:
{
return x_200;
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_66);
lean_dec_ref(x_61);
lean_del_object(x_36);
x_205 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__20);
lean_inc_ref(x_27);
x_206 = l_Lean_mkApp3(x_205, x_27, x_24, x_62);
x_207 = l_Lean_Meta_Sym_shareCommon___redArg(x_206, x_7);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = l_Lean_Meta_Sym_getTrueExpr___redArg(x_6);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
x_211 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__23);
x_212 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_213 = 0;
x_214 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_215 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_208);
lean_inc(x_210);
lean_inc_ref(x_27);
x_216 = l_Lean_mkApp4(x_214, x_27, x_210, x_208, x_215);
x_217 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_218 = lean_array_push(x_217, x_216);
x_219 = lean_unbox(x_42);
x_220 = lean_unbox(x_42);
x_221 = l_Lean_Expr_betaRev(x_21, x_218, x_219, x_220);
lean_dec_ref(x_218);
lean_inc(x_210);
x_222 = l_Lean_mkLambda(x_212, x_213, x_210, x_221);
x_223 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_222, x_7);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec_ref(x_223);
lean_inc(x_210);
x_225 = l_Lean_mkNot(x_210);
x_226 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_208);
lean_inc(x_210);
x_227 = l_Lean_mkApp4(x_226, x_27, x_210, x_208, x_215);
x_228 = lean_array_push(x_217, x_227);
x_229 = lean_unbox(x_42);
x_230 = lean_unbox(x_42);
x_231 = l_Lean_Expr_betaRev(x_18, x_228, x_229, x_230);
lean_dec_ref(x_228);
x_232 = l_Lean_mkLambda(x_212, x_213, x_225, x_231);
x_233 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_232, x_7);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
lean_dec_ref(x_233);
x_235 = lean_unsigned_to_nat(4u);
x_236 = l_Lean_Expr_getBoundedAppFn(x_235, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_234);
lean_inc(x_224);
lean_inc(x_210);
x_237 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_236, x_210, x_211, x_224, x_234, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
x_239 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25);
x_240 = lean_unbox(x_42);
x_241 = lean_unbox(x_42);
lean_inc(x_224);
x_242 = l_Lean_Expr_betaRev(x_224, x_239, x_240, x_241);
x_243 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_242, x_7);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
lean_inc_ref(x_2);
x_246 = l_Lean_Expr_replaceFn(x_2, x_245);
x_247 = l_Lean_mkApp3(x_246, x_210, x_211, x_208);
x_248 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_249 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_250 = l_Lean_mkConst(x_248, x_249);
x_251 = l_Lean_mkApp3(x_250, x_30, x_224, x_234);
lean_inc(x_244);
x_252 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_2, x_238, x_247, x_244, x_251, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; uint8_t x_264; 
x_253 = lean_ctor_get(x_252, 0);
x_264 = !lean_is_exclusive(x_252);
if (x_264 == 0)
{
x_254 = x_252;
x_255 = x_264;
goto block_263;
}
else
{
lean_inc(x_253);
lean_dec(x_252);
x_254 = lean_box(0);
x_255 = x_264;
goto block_263;
}
block_263:
{
lean_object* x_256; 
if (x_64 == 0)
{
lean_ctor_set(x_63, 1, x_253);
lean_ctor_set(x_63, 0, x_244);
x_256 = x_63;
goto block_261;
}
else
{
lean_object* x_262; 
x_262 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_262, 0, x_244);
lean_ctor_set(x_262, 1, x_253);
x_256 = x_262;
goto block_261;
}
block_261:
{
uint8_t x_257; lean_object* x_258; 
x_257 = lean_unbox(x_42);
lean_dec(x_42);
lean_ctor_set_uint8(x_256, sizeof(void*)*2, x_257);
if (x_255 == 0)
{
lean_ctor_set(x_254, 0, x_256);
x_258 = x_254;
goto block_259;
}
else
{
lean_object* x_260; 
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_256);
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
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; uint8_t x_272; 
lean_dec(x_244);
lean_del_object(x_63);
lean_dec(x_42);
x_265 = lean_ctor_get(x_252, 0);
x_272 = !lean_is_exclusive(x_252);
if (x_272 == 0)
{
x_266 = x_252;
x_267 = x_272;
goto block_271;
}
else
{
lean_inc(x_265);
lean_dec(x_252);
x_266 = lean_box(0);
x_267 = x_272;
goto block_271;
}
block_271:
{
lean_object* x_268; 
if (x_267 == 0)
{
x_268 = x_266;
goto block_269;
}
else
{
lean_object* x_270; 
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_265);
x_268 = x_270;
goto block_269;
}
block_269:
{
return x_268;
}
}
}
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; uint8_t x_280; 
lean_dec(x_238);
lean_dec(x_234);
lean_dec(x_224);
lean_dec(x_210);
lean_dec(x_208);
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_273 = lean_ctor_get(x_243, 0);
x_280 = !lean_is_exclusive(x_243);
if (x_280 == 0)
{
x_274 = x_243;
x_275 = x_280;
goto block_279;
}
else
{
lean_inc(x_273);
lean_dec(x_243);
x_274 = lean_box(0);
x_275 = x_280;
goto block_279;
}
block_279:
{
lean_object* x_276; 
if (x_275 == 0)
{
x_276 = x_274;
goto block_277;
}
else
{
lean_object* x_278; 
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_273);
x_276 = x_278;
goto block_277;
}
block_277:
{
return x_276;
}
}
}
}
else
{
lean_object* x_281; lean_object* x_282; uint8_t x_283; uint8_t x_288; 
lean_dec(x_234);
lean_dec(x_224);
lean_dec(x_210);
lean_dec(x_208);
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
x_281 = lean_ctor_get(x_237, 0);
x_288 = !lean_is_exclusive(x_237);
if (x_288 == 0)
{
x_282 = x_237;
x_283 = x_288;
goto block_287;
}
else
{
lean_inc(x_281);
lean_dec(x_237);
x_282 = lean_box(0);
x_283 = x_288;
goto block_287;
}
block_287:
{
lean_object* x_284; 
if (x_283 == 0)
{
x_284 = x_282;
goto block_285;
}
else
{
lean_object* x_286; 
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_281);
x_284 = x_286;
goto block_285;
}
block_285:
{
return x_284;
}
}
}
}
else
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_296; 
lean_dec(x_224);
lean_dec(x_210);
lean_dec(x_208);
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_289 = lean_ctor_get(x_233, 0);
x_296 = !lean_is_exclusive(x_233);
if (x_296 == 0)
{
x_290 = x_233;
x_291 = x_296;
goto block_295;
}
else
{
lean_inc(x_289);
lean_dec(x_233);
x_290 = lean_box(0);
x_291 = x_296;
goto block_295;
}
block_295:
{
lean_object* x_292; 
if (x_291 == 0)
{
x_292 = x_290;
goto block_293;
}
else
{
lean_object* x_294; 
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_289);
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
else
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; uint8_t x_304; 
lean_dec(x_210);
lean_dec(x_208);
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_297 = lean_ctor_get(x_223, 0);
x_304 = !lean_is_exclusive(x_223);
if (x_304 == 0)
{
x_298 = x_223;
x_299 = x_304;
goto block_303;
}
else
{
lean_inc(x_297);
lean_dec(x_223);
x_298 = lean_box(0);
x_299 = x_304;
goto block_303;
}
block_303:
{
lean_object* x_300; 
if (x_299 == 0)
{
x_300 = x_298;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_297);
x_300 = x_302;
goto block_301;
}
block_301:
{
return x_300;
}
}
}
}
else
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_312; 
lean_dec(x_208);
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_305 = lean_ctor_get(x_209, 0);
x_312 = !lean_is_exclusive(x_209);
if (x_312 == 0)
{
x_306 = x_209;
x_307 = x_312;
goto block_311;
}
else
{
lean_inc(x_305);
lean_dec(x_209);
x_306 = lean_box(0);
x_307 = x_312;
goto block_311;
}
block_311:
{
lean_object* x_308; 
if (x_307 == 0)
{
x_308 = x_306;
goto block_309;
}
else
{
lean_object* x_310; 
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_305);
x_308 = x_310;
goto block_309;
}
block_309:
{
return x_308;
}
}
}
}
else
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; uint8_t x_320; 
lean_del_object(x_63);
lean_dec(x_42);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_313 = lean_ctor_get(x_207, 0);
x_320 = !lean_is_exclusive(x_207);
if (x_320 == 0)
{
x_314 = x_207;
x_315 = x_320;
goto block_319;
}
else
{
lean_inc(x_313);
lean_dec(x_207);
x_314 = lean_box(0);
x_315 = x_320;
goto block_319;
}
block_319:
{
lean_object* x_316; 
if (x_315 == 0)
{
x_316 = x_314;
goto block_317;
}
else
{
lean_object* x_318; 
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_313);
x_316 = x_318;
goto block_317;
}
block_317:
{
return x_316;
}
}
}
}
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; uint8_t x_328; 
lean_del_object(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec(x_42);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_321 = lean_ctor_get(x_65, 0);
x_328 = !lean_is_exclusive(x_65);
if (x_328 == 0)
{
x_322 = x_65;
x_323 = x_328;
goto block_327;
}
else
{
lean_inc(x_321);
lean_dec(x_65);
x_322 = lean_box(0);
x_323 = x_328;
goto block_327;
}
block_327:
{
lean_object* x_324; 
if (x_323 == 0)
{
x_324 = x_322;
goto block_325;
}
else
{
lean_object* x_326; 
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_321);
x_324 = x_326;
goto block_325;
}
block_325:
{
return x_324;
}
}
}
}
}
}
}
else
{
lean_dec(x_42);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_47;
}
}
else
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; uint8_t x_340; 
lean_dec(x_42);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_333 = lean_ctor_get(x_45, 0);
x_340 = !lean_is_exclusive(x_45);
if (x_340 == 0)
{
x_334 = x_45;
x_335 = x_340;
goto block_339;
}
else
{
lean_inc(x_333);
lean_dec(x_45);
x_334 = lean_box(0);
x_335 = x_340;
goto block_339;
}
block_339:
{
lean_object* x_336; 
if (x_335 == 0)
{
x_336 = x_334;
goto block_337;
}
else
{
lean_object* x_338; 
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_333);
x_336 = x_338;
goto block_337;
}
block_337:
{
return x_336;
}
}
}
}
else
{
lean_object* x_341; uint8_t x_342; uint8_t x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_42);
lean_del_object(x_36);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_341 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16);
x_342 = lean_unbox(x_39);
x_343 = lean_unbox(x_39);
lean_inc_ref(x_18);
x_344 = l_Lean_Expr_betaRev(x_18, x_341, x_342, x_343);
x_345 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_344, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; uint8_t x_348; uint8_t x_359; 
x_346 = lean_ctor_get(x_345, 0);
x_359 = !lean_is_exclusive(x_345);
if (x_359 == 0)
{
x_347 = x_345;
x_348 = x_359;
goto block_358;
}
else
{
lean_inc(x_346);
lean_dec(x_345);
x_347 = lean_box(0);
x_348 = x_359;
goto block_358;
}
block_358:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; lean_object* x_355; 
x_349 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__20));
x_350 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_351 = l_Lean_mkConst(x_349, x_350);
x_352 = l_Lean_mkApp3(x_351, x_30, x_21, x_18);
x_353 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_353, 0, x_346);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_unbox(x_39);
lean_dec(x_39);
lean_ctor_set_uint8(x_353, sizeof(void*)*2, x_354);
if (x_348 == 0)
{
lean_ctor_set(x_347, 0, x_353);
x_355 = x_347;
goto block_356;
}
else
{
lean_object* x_357; 
x_357 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_357, 0, x_353);
x_355 = x_357;
goto block_356;
}
block_356:
{
return x_355;
}
}
}
else
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_367; 
lean_dec(x_39);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_360 = lean_ctor_get(x_345, 0);
x_367 = !lean_is_exclusive(x_345);
if (x_367 == 0)
{
x_361 = x_345;
x_362 = x_367;
goto block_366;
}
else
{
lean_inc(x_360);
lean_dec(x_345);
x_361 = lean_box(0);
x_362 = x_367;
goto block_366;
}
block_366:
{
lean_object* x_363; 
if (x_362 == 0)
{
x_363 = x_361;
goto block_364;
}
else
{
lean_object* x_365; 
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_360);
x_363 = x_365;
goto block_364;
}
block_364:
{
return x_363;
}
}
}
}
}
else
{
lean_object* x_368; lean_object* x_369; uint8_t x_370; uint8_t x_375; 
lean_dec(x_39);
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_368 = lean_ctor_get(x_41, 0);
x_375 = !lean_is_exclusive(x_41);
if (x_375 == 0)
{
x_369 = x_41;
x_370 = x_375;
goto block_374;
}
else
{
lean_inc(x_368);
lean_dec(x_41);
x_369 = lean_box(0);
x_370 = x_375;
goto block_374;
}
block_374:
{
lean_object* x_371; 
if (x_370 == 0)
{
x_371 = x_369;
goto block_372;
}
else
{
lean_object* x_373; 
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_368);
x_371 = x_373;
goto block_372;
}
block_372:
{
return x_371;
}
}
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_39);
lean_del_object(x_36);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_376 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__25);
lean_inc_ref(x_21);
x_377 = l_Lean_Expr_betaRev(x_21, x_376, x_1, x_1);
x_378 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_377, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; uint8_t x_391; 
x_379 = lean_ctor_get(x_378, 0);
x_391 = !lean_is_exclusive(x_378);
if (x_391 == 0)
{
x_380 = x_378;
x_381 = x_391;
goto block_390;
}
else
{
lean_inc(x_379);
lean_dec(x_378);
x_380 = lean_box(0);
x_381 = x_391;
goto block_390;
}
block_390:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_382 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__27));
x_383 = l_Lean_Expr_constLevels_x21(x_31);
lean_dec_ref(x_31);
x_384 = l_Lean_mkConst(x_382, x_383);
x_385 = l_Lean_mkApp3(x_384, x_30, x_21, x_18);
x_386 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_386, 0, x_379);
lean_ctor_set(x_386, 1, x_385);
lean_ctor_set_uint8(x_386, sizeof(void*)*2, x_1);
if (x_381 == 0)
{
lean_ctor_set(x_380, 0, x_386);
x_387 = x_380;
goto block_388;
}
else
{
lean_object* x_389; 
x_389 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_389, 0, x_386);
x_387 = x_389;
goto block_388;
}
block_388:
{
return x_387;
}
}
}
else
{
lean_object* x_392; lean_object* x_393; uint8_t x_394; uint8_t x_399; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
x_392 = lean_ctor_get(x_378, 0);
x_399 = !lean_is_exclusive(x_378);
if (x_399 == 0)
{
x_393 = x_378;
x_394 = x_399;
goto block_398;
}
else
{
lean_inc(x_392);
lean_dec(x_378);
x_393 = lean_box(0);
x_394 = x_399;
goto block_398;
}
block_398:
{
lean_object* x_395; 
if (x_394 == 0)
{
x_395 = x_393;
goto block_396;
}
else
{
lean_object* x_397; 
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_392);
x_395 = x_397;
goto block_396;
}
block_396:
{
return x_395;
}
}
}
}
}
else
{
lean_object* x_400; lean_object* x_401; uint8_t x_402; uint8_t x_407; 
lean_del_object(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_400 = lean_ctor_get(x_38, 0);
x_407 = !lean_is_exclusive(x_38);
if (x_407 == 0)
{
x_401 = x_38;
x_402 = x_407;
goto block_406;
}
else
{
lean_inc(x_400);
lean_dec(x_38);
x_401 = lean_box(0);
x_402 = x_407;
goto block_406;
}
block_406:
{
lean_object* x_403; 
if (x_402 == 0)
{
x_403 = x_401;
goto block_404;
}
else
{
lean_object* x_405; 
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_400);
x_403 = x_405;
goto block_404;
}
block_404:
{
return x_403;
}
}
}
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; uint8_t x_591; 
lean_dec_ref(x_31);
lean_dec_ref(x_30);
x_410 = lean_ctor_get(x_35, 0);
x_411 = lean_ctor_get(x_35, 1);
x_591 = !lean_is_exclusive(x_35);
if (x_591 == 0)
{
x_412 = x_35;
x_413 = x_591;
goto block_590;
}
else
{
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_35);
x_412 = lean_box(0);
x_413 = x_591;
goto block_590;
}
block_590:
{
lean_object* x_414; 
x_414 = l_Lean_Meta_Sym_isTrueExpr___redArg(x_410, x_6);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; uint8_t x_416; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
lean_dec_ref(x_414);
x_416 = lean_unbox(x_415);
if (x_416 == 0)
{
lean_object* x_417; 
x_417 = l_Lean_Meta_Sym_isFalseExpr___redArg(x_410, x_6);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; uint8_t x_419; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
lean_dec_ref(x_417);
x_419 = lean_unbox(x_418);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_415);
x_420 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28, &l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28_once, _init_l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__28);
lean_inc_ref(x_411);
lean_inc_ref(x_410);
lean_inc_ref(x_27);
x_421 = l_Lean_mkApp4(x_420, x_27, x_410, x_24, x_411);
x_422 = l_Lean_Meta_Sym_shareCommon___redArg(x_411, x_7);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
lean_dec_ref(x_422);
x_424 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
x_425 = 0;
x_426 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7);
x_427 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8);
lean_inc(x_423);
lean_inc_ref(x_410);
lean_inc_ref(x_27);
x_428 = l_Lean_mkApp4(x_426, x_27, x_410, x_423, x_427);
x_429 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_430 = lean_array_push(x_429, x_428);
x_431 = lean_unbox(x_418);
x_432 = lean_unbox(x_418);
x_433 = l_Lean_Expr_betaRev(x_21, x_430, x_431, x_432);
lean_dec_ref(x_430);
lean_inc_ref(x_410);
x_434 = l_Lean_mkLambda(x_424, x_425, x_410, x_433);
x_435 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_434, x_7);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
lean_dec_ref(x_435);
lean_inc_ref(x_410);
x_437 = l_Lean_mkNot(x_410);
x_438 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12);
lean_inc(x_423);
lean_inc_ref(x_410);
x_439 = l_Lean_mkApp4(x_438, x_27, x_410, x_423, x_427);
x_440 = lean_array_push(x_429, x_439);
x_441 = lean_unbox(x_418);
x_442 = lean_unbox(x_418);
x_443 = l_Lean_Expr_betaRev(x_18, x_440, x_441, x_442);
lean_dec_ref(x_440);
x_444 = l_Lean_mkLambda(x_424, x_425, x_437, x_443);
x_445 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_444, x_7);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
lean_dec_ref(x_445);
x_447 = lean_unsigned_to_nat(4u);
x_448 = l_Lean_Expr_getBoundedAppFn(x_447, x_2);
lean_inc_ref(x_421);
lean_inc_ref(x_410);
x_449 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Simp_simpIteCbv_spec__1(x_448, x_410, x_421, x_436, x_446, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; uint8_t x_452; uint8_t x_464; 
x_450 = lean_ctor_get(x_449, 0);
x_464 = !lean_is_exclusive(x_449);
if (x_464 == 0)
{
x_451 = x_449;
x_452 = x_464;
goto block_463;
}
else
{
lean_inc(x_450);
lean_dec(x_449);
x_451 = lean_box(0);
x_452 = x_464;
goto block_463;
}
block_463:
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_453 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__18));
x_454 = l_Lean_Expr_replaceFn(x_2, x_453);
x_455 = l_Lean_mkApp3(x_454, x_410, x_421, x_423);
if (x_413 == 0)
{
lean_ctor_set(x_412, 1, x_455);
lean_ctor_set(x_412, 0, x_450);
x_456 = x_412;
goto block_461;
}
else
{
lean_object* x_462; 
x_462 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_462, 0, x_450);
lean_ctor_set(x_462, 1, x_455);
x_456 = x_462;
goto block_461;
}
block_461:
{
uint8_t x_457; lean_object* x_458; 
x_457 = lean_unbox(x_418);
lean_dec(x_418);
lean_ctor_set_uint8(x_456, sizeof(void*)*2, x_457);
if (x_452 == 0)
{
lean_ctor_set(x_451, 0, x_456);
x_458 = x_451;
goto block_459;
}
else
{
lean_object* x_460; 
x_460 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_460, 0, x_456);
x_458 = x_460;
goto block_459;
}
block_459:
{
return x_458;
}
}
}
}
else
{
lean_object* x_465; lean_object* x_466; uint8_t x_467; uint8_t x_472; 
lean_dec(x_423);
lean_dec_ref(x_421);
lean_dec(x_418);
lean_del_object(x_412);
lean_dec_ref(x_410);
lean_dec_ref(x_2);
x_465 = lean_ctor_get(x_449, 0);
x_472 = !lean_is_exclusive(x_449);
if (x_472 == 0)
{
x_466 = x_449;
x_467 = x_472;
goto block_471;
}
else
{
lean_inc(x_465);
lean_dec(x_449);
x_466 = lean_box(0);
x_467 = x_472;
goto block_471;
}
block_471:
{
lean_object* x_468; 
if (x_467 == 0)
{
x_468 = x_466;
goto block_469;
}
else
{
lean_object* x_470; 
x_470 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_470, 0, x_465);
x_468 = x_470;
goto block_469;
}
block_469:
{
return x_468;
}
}
}
}
else
{
lean_object* x_473; lean_object* x_474; uint8_t x_475; uint8_t x_480; 
lean_dec(x_436);
lean_dec(x_423);
lean_dec_ref(x_421);
lean_dec(x_418);
lean_del_object(x_412);
lean_dec_ref(x_410);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_473 = lean_ctor_get(x_445, 0);
x_480 = !lean_is_exclusive(x_445);
if (x_480 == 0)
{
x_474 = x_445;
x_475 = x_480;
goto block_479;
}
else
{
lean_inc(x_473);
lean_dec(x_445);
x_474 = lean_box(0);
x_475 = x_480;
goto block_479;
}
block_479:
{
lean_object* x_476; 
if (x_475 == 0)
{
x_476 = x_474;
goto block_477;
}
else
{
lean_object* x_478; 
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_473);
x_476 = x_478;
goto block_477;
}
block_477:
{
return x_476;
}
}
}
}
else
{
lean_object* x_481; lean_object* x_482; uint8_t x_483; uint8_t x_488; 
lean_dec(x_423);
lean_dec_ref(x_421);
lean_dec(x_418);
lean_del_object(x_412);
lean_dec_ref(x_410);
lean_dec_ref(x_27);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_481 = lean_ctor_get(x_435, 0);
x_488 = !lean_is_exclusive(x_435);
if (x_488 == 0)
{
x_482 = x_435;
x_483 = x_488;
goto block_487;
}
else
{
lean_inc(x_481);
lean_dec(x_435);
x_482 = lean_box(0);
x_483 = x_488;
goto block_487;
}
block_487:
{
lean_object* x_484; 
if (x_483 == 0)
{
x_484 = x_482;
goto block_485;
}
else
{
lean_object* x_486; 
x_486 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_486, 0, x_481);
x_484 = x_486;
goto block_485;
}
block_485:
{
return x_484;
}
}
}
}
else
{
lean_object* x_489; lean_object* x_490; uint8_t x_491; uint8_t x_496; 
lean_dec_ref(x_421);
lean_dec(x_418);
lean_del_object(x_412);
lean_dec_ref(x_410);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_489 = lean_ctor_get(x_422, 0);
x_496 = !lean_is_exclusive(x_422);
if (x_496 == 0)
{
x_490 = x_422;
x_491 = x_496;
goto block_495;
}
else
{
lean_inc(x_489);
lean_dec(x_422);
x_490 = lean_box(0);
x_491 = x_496;
goto block_495;
}
block_495:
{
lean_object* x_492; 
if (x_491 == 0)
{
x_492 = x_490;
goto block_493;
}
else
{
lean_object* x_494; 
x_494 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_494, 0, x_489);
x_492 = x_494;
goto block_493;
}
block_493:
{
return x_492;
}
}
}
}
else
{
lean_object* x_497; lean_object* x_498; 
lean_dec(x_418);
lean_dec_ref(x_410);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_411);
x_497 = l_Lean_Meta_mkOfEqFalseCore(x_27, x_411);
x_498 = l_Lean_Meta_Sym_shareCommon___redArg(x_497, x_7);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; uint8_t x_503; lean_object* x_504; lean_object* x_505; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
lean_dec_ref(x_498);
x_500 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_501 = lean_array_push(x_500, x_499);
x_502 = lean_unbox(x_415);
x_503 = lean_unbox(x_415);
x_504 = l_Lean_Expr_betaRev(x_18, x_501, x_502, x_503);
lean_dec_ref(x_501);
x_505 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_504, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; uint8_t x_508; uint8_t x_520; 
x_506 = lean_ctor_get(x_505, 0);
x_520 = !lean_is_exclusive(x_505);
if (x_520 == 0)
{
x_507 = x_505;
x_508 = x_520;
goto block_519;
}
else
{
lean_inc(x_506);
lean_dec(x_505);
x_507 = lean_box(0);
x_508 = x_520;
goto block_519;
}
block_519:
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_509 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__29));
x_510 = l_Lean_Expr_replaceFn(x_2, x_509);
x_511 = l_Lean_Expr_app___override(x_510, x_411);
if (x_413 == 0)
{
lean_ctor_set(x_412, 1, x_511);
lean_ctor_set(x_412, 0, x_506);
x_512 = x_412;
goto block_517;
}
else
{
lean_object* x_518; 
x_518 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_518, 0, x_506);
lean_ctor_set(x_518, 1, x_511);
x_512 = x_518;
goto block_517;
}
block_517:
{
uint8_t x_513; lean_object* x_514; 
x_513 = lean_unbox(x_415);
lean_dec(x_415);
lean_ctor_set_uint8(x_512, sizeof(void*)*2, x_513);
if (x_508 == 0)
{
lean_ctor_set(x_507, 0, x_512);
x_514 = x_507;
goto block_515;
}
else
{
lean_object* x_516; 
x_516 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_516, 0, x_512);
x_514 = x_516;
goto block_515;
}
block_515:
{
return x_514;
}
}
}
}
else
{
lean_object* x_521; lean_object* x_522; uint8_t x_523; uint8_t x_528; 
lean_dec(x_415);
lean_del_object(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_2);
x_521 = lean_ctor_get(x_505, 0);
x_528 = !lean_is_exclusive(x_505);
if (x_528 == 0)
{
x_522 = x_505;
x_523 = x_528;
goto block_527;
}
else
{
lean_inc(x_521);
lean_dec(x_505);
x_522 = lean_box(0);
x_523 = x_528;
goto block_527;
}
block_527:
{
lean_object* x_524; 
if (x_523 == 0)
{
x_524 = x_522;
goto block_525;
}
else
{
lean_object* x_526; 
x_526 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_526, 0, x_521);
x_524 = x_526;
goto block_525;
}
block_525:
{
return x_524;
}
}
}
}
else
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; uint8_t x_536; 
lean_dec(x_415);
lean_del_object(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_18);
lean_dec(x_7);
lean_dec_ref(x_2);
x_529 = lean_ctor_get(x_498, 0);
x_536 = !lean_is_exclusive(x_498);
if (x_536 == 0)
{
x_530 = x_498;
x_531 = x_536;
goto block_535;
}
else
{
lean_inc(x_529);
lean_dec(x_498);
x_530 = lean_box(0);
x_531 = x_536;
goto block_535;
}
block_535:
{
lean_object* x_532; 
if (x_531 == 0)
{
x_532 = x_530;
goto block_533;
}
else
{
lean_object* x_534; 
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_529);
x_532 = x_534;
goto block_533;
}
block_533:
{
return x_532;
}
}
}
}
}
else
{
lean_object* x_537; lean_object* x_538; uint8_t x_539; uint8_t x_544; 
lean_dec(x_415);
lean_del_object(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_537 = lean_ctor_get(x_417, 0);
x_544 = !lean_is_exclusive(x_417);
if (x_544 == 0)
{
x_538 = x_417;
x_539 = x_544;
goto block_543;
}
else
{
lean_inc(x_537);
lean_dec(x_417);
x_538 = lean_box(0);
x_539 = x_544;
goto block_543;
}
block_543:
{
lean_object* x_540; 
if (x_539 == 0)
{
x_540 = x_538;
goto block_541;
}
else
{
lean_object* x_542; 
x_542 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_542, 0, x_537);
x_540 = x_542;
goto block_541;
}
block_541:
{
return x_540;
}
}
}
}
else
{
lean_object* x_545; lean_object* x_546; 
lean_dec(x_415);
lean_dec_ref(x_410);
lean_dec_ref(x_24);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_411);
x_545 = l_Lean_Meta_mkOfEqTrueCore(x_27, x_411);
x_546 = l_Lean_Meta_Sym_shareCommon___redArg(x_545, x_7);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
lean_dec_ref(x_546);
x_548 = lean_obj_once(&l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
x_549 = lean_array_push(x_548, x_547);
x_550 = l_Lean_Expr_betaRev(x_21, x_549, x_1, x_1);
lean_dec_ref(x_549);
x_551 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_550, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; uint8_t x_554; uint8_t x_565; 
x_552 = lean_ctor_get(x_551, 0);
x_565 = !lean_is_exclusive(x_551);
if (x_565 == 0)
{
x_553 = x_551;
x_554 = x_565;
goto block_564;
}
else
{
lean_inc(x_552);
lean_dec(x_551);
x_553 = lean_box(0);
x_554 = x_565;
goto block_564;
}
block_564:
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_555 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__31));
x_556 = l_Lean_Expr_replaceFn(x_2, x_555);
x_557 = l_Lean_Expr_app___override(x_556, x_411);
if (x_413 == 0)
{
lean_ctor_set(x_412, 1, x_557);
lean_ctor_set(x_412, 0, x_552);
x_558 = x_412;
goto block_562;
}
else
{
lean_object* x_563; 
x_563 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_563, 0, x_552);
lean_ctor_set(x_563, 1, x_557);
x_558 = x_563;
goto block_562;
}
block_562:
{
lean_object* x_559; 
lean_ctor_set_uint8(x_558, sizeof(void*)*2, x_1);
if (x_554 == 0)
{
lean_ctor_set(x_553, 0, x_558);
x_559 = x_553;
goto block_560;
}
else
{
lean_object* x_561; 
x_561 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_561, 0, x_558);
x_559 = x_561;
goto block_560;
}
block_560:
{
return x_559;
}
}
}
}
else
{
lean_object* x_566; lean_object* x_567; uint8_t x_568; uint8_t x_573; 
lean_del_object(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_2);
x_566 = lean_ctor_get(x_551, 0);
x_573 = !lean_is_exclusive(x_551);
if (x_573 == 0)
{
x_567 = x_551;
x_568 = x_573;
goto block_572;
}
else
{
lean_inc(x_566);
lean_dec(x_551);
x_567 = lean_box(0);
x_568 = x_573;
goto block_572;
}
block_572:
{
lean_object* x_569; 
if (x_568 == 0)
{
x_569 = x_567;
goto block_570;
}
else
{
lean_object* x_571; 
x_571 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_571, 0, x_566);
x_569 = x_571;
goto block_570;
}
block_570:
{
return x_569;
}
}
}
}
else
{
lean_object* x_574; lean_object* x_575; uint8_t x_576; uint8_t x_581; 
lean_del_object(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_2);
x_574 = lean_ctor_get(x_546, 0);
x_581 = !lean_is_exclusive(x_546);
if (x_581 == 0)
{
x_575 = x_546;
x_576 = x_581;
goto block_580;
}
else
{
lean_inc(x_574);
lean_dec(x_546);
x_575 = lean_box(0);
x_576 = x_581;
goto block_580;
}
block_580:
{
lean_object* x_577; 
if (x_576 == 0)
{
x_577 = x_575;
goto block_578;
}
else
{
lean_object* x_579; 
x_579 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_579, 0, x_574);
x_577 = x_579;
goto block_578;
}
block_578:
{
return x_577;
}
}
}
}
}
else
{
lean_object* x_582; lean_object* x_583; uint8_t x_584; uint8_t x_589; 
lean_del_object(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_410);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_582 = lean_ctor_get(x_414, 0);
x_589 = !lean_is_exclusive(x_414);
if (x_589 == 0)
{
x_583 = x_414;
x_584 = x_589;
goto block_588;
}
else
{
lean_inc(x_582);
lean_dec(x_414);
x_583 = lean_box(0);
x_584 = x_589;
goto block_588;
}
block_588:
{
lean_object* x_585; 
if (x_584 == 0)
{
x_585 = x_583;
goto block_586;
}
else
{
lean_object* x_587; 
x_587 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_587, 0, x_582);
x_585 = x_587;
goto block_586;
}
block_586:
{
return x_585;
}
}
}
}
}
}
else
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_34;
}
}
}
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Expr_getAppNumArgs(x_1);
x_13 = lean_unsigned_to_nat(5u);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed), 12, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_18 = l_Lean_Meta_Sym_Simp_propagateOverApplied(x_1, x_17, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_19, 0, x_14);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Simp_simpDIteCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_get_reducibility_status(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_21; 
x_5 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(x_1, x_3);
x_6 = lean_ctor_get(x_5, 0);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
x_7 = x_5;
x_8 = x_21;
goto block_20;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_21;
goto block_20;
}
block_20:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
if (x_9 == 2)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_11);
x_12 = x_7;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
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
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_box(x_15);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_16);
x_17 = x_7;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ConstantInfo_name(x_3);
x_8 = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_11; 
lean_dec_ref(x_3);
x_11 = lean_ctor_get_uint8(x_2, 9);
lean_dec_ref(x_2);
switch (x_11) {
case 4:
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_8;
}
case 0:
{
lean_object* x_12; uint8_t x_13; uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_8, 0);
lean_dec(x_21);
x_12 = x_8;
x_13 = x_20;
goto block_19;
}
else
{
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = x_20;
goto block_19;
}
block_19:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_15);
x_16 = x_12;
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
case 1:
{
lean_object* x_22; 
lean_dec_ref(x_8);
x_22 = l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(x_7, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_36; 
x_23 = lean_ctor_get(x_22, 0);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
x_24 = x_22;
x_25 = x_36;
goto block_35;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_26; 
x_26 = lean_unbox(x_23);
lean_dec(x_23);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
x_27 = 1;
x_28 = lean_box(x_27);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_28);
x_29 = x_24;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
else
{
lean_object* x_32; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_9);
x_32 = x_24;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_9);
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
else
{
lean_dec(x_9);
return x_22;
}
}
default: 
{
lean_object* x_37; uint8_t x_38; uint8_t x_69; 
lean_dec(x_9);
lean_dec_ref(x_4);
x_69 = !lean_is_exclusive(x_8);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_8, 0);
lean_dec(x_70);
x_37 = x_8;
x_38 = x_69;
goto block_68;
}
else
{
lean_dec(x_8);
x_37 = lean_box(0);
x_38 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_67; 
x_39 = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(x_7, x_5);
lean_dec(x_5);
x_40 = lean_ctor_get(x_39, 0);
x_67 = !lean_is_exclusive(x_39);
if (x_67 == 0)
{
x_41 = x_39;
x_42 = x_67;
goto block_66;
}
else
{
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = x_67;
goto block_66;
}
block_66:
{
uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; 
x_43 = 0;
x_44 = lean_unbox(x_40);
x_45 = l_Lean_instBEqReducibilityStatus_beq(x_44, x_43);
x_46 = 1;
if (x_45 == 0)
{
uint8_t x_57; uint8_t x_58; 
lean_del_object(x_37);
x_57 = 3;
x_58 = l_Lean_Meta_instBEqTransparencyMode_beq(x_11, x_57);
if (x_58 == 0)
{
lean_dec(x_40);
x_47 = x_58;
goto block_56;
}
else
{
uint8_t x_59; uint8_t x_60; uint8_t x_61; 
x_59 = 3;
x_60 = lean_unbox(x_40);
lean_dec(x_40);
x_61 = l_Lean_instBEqReducibilityStatus_beq(x_60, x_59);
x_47 = x_61;
goto block_56;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_del_object(x_41);
lean_dec(x_40);
x_62 = lean_box(x_46);
if (x_38 == 0)
{
lean_ctor_set(x_37, 0, x_62);
x_63 = x_37;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
block_56:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(x_47);
if (x_42 == 0)
{
lean_ctor_set(x_41, 0, x_48);
x_49 = x_41;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(x_46);
if (x_42 == 0)
{
lean_ctor_set(x_41, 0, x_52);
x_53 = x_41;
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
}
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
lean_dec_ref(x_1);
x_72 = lean_apply_5(x_71, x_2, x_3, x_4, x_5, lean_box(0));
return x_72;
}
}
else
{
lean_object* x_73; uint8_t x_74; uint8_t x_81; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_8);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_8, 0);
lean_dec(x_82);
x_73 = x_8;
x_74 = x_81;
goto block_80;
}
else
{
lean_dec(x_8);
x_73 = lean_box(0);
x_74 = x_81;
goto block_80;
}
block_80:
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_box(x_75);
if (x_74 == 0)
{
lean_ctor_set(x_73, 0, x_76);
x_77 = x_73;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_76);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_27; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 3);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
x_18 = x_2;
x_19 = x_27;
goto block_26;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_20, 0, x_14);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (x_19 == 0)
{
lean_ctor_set(x_18, 6, x_21);
x_22 = x_18;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 2, x_10);
lean_ctor_set(x_25, 3, x_11);
lean_ctor_set(x_25, 4, x_12);
lean_ctor_set(x_25, 5, x_13);
lean_ctor_set(x_25, 6, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*7, x_8);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 1, x_15);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 2, x_16);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 3, x_17);
x_22 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_23; 
x_23 = lean_apply_5(x_1, x_22, x_3, x_4, x_5, lean_box(0));
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_13 = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0));
x_16 = l_Lean_Meta_Sym_Simp_Theorems_rewrite(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_17 = lean_ctor_get(x_13, 0);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
x_18 = x_13;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_13);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___boxed), 6, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_9 = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_38; 
x_10 = lean_ctor_get(x_9, 0);
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
x_11 = x_9;
x_12 = x_38;
goto block_37;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_38;
goto block_37;
}
block_37:
{
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_del_object(x_11);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
lean_inc(x_13);
x_14 = l_Lean_Meta_Sym_mkEqRefl___redArg(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_15 = lean_ctor_get(x_14, 0);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
x_16 = x_14;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
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
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_13);
x_25 = lean_ctor_get(x_14, 0);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
x_26 = x_14;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_33 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_33);
x_34 = x_11;
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
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_39 = lean_ctor_get(x_9, 0);
x_46 = !lean_is_exclusive(x_9);
if (x_46 == 0)
{
x_40 = x_9;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_9);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(x_1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_17; 
x_17 = l_Lean_Expr_isApp(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Expr_getAppFn(x_1);
x_21 = l_Lean_Expr_constName_x3f(x_20);
lean_dec_ref(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_89; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_22);
x_23 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(x_22, x_10);
x_24 = lean_ctor_get(x_23, 0);
x_89 = !lean_is_exclusive(x_23);
if (x_89 == 0)
{
x_25 = x_23;
x_26 = x_89;
goto block_88;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_89;
goto block_88;
}
block_88:
{
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_del_object(x_25);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec_ref(x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_28, x_30);
lean_dec(x_28);
x_32 = lean_nat_add(x_31, x_29);
lean_dec(x_29);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_33 = l_Lean_Meta_Sym_Simp_simpAppArgRange(x_1, x_31, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = lean_ctor_get_uint8(x_34, 0);
lean_dec_ref(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec_ref(x_33);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
x_36 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(x_22, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = x_36;
goto block_16;
}
else
{
lean_dec(x_22);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = x_33;
goto block_16;
}
}
else
{
uint8_t x_37; 
x_37 = lean_ctor_get_uint8(x_34, sizeof(void*)*2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_83; 
lean_dec_ref(x_33);
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
x_83 = !lean_is_exclusive(x_34);
if (x_83 == 0)
{
x_40 = x_34;
x_41 = x_83;
goto block_82;
}
else
{
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_42; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_38);
x_42 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(x_22, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_81; 
x_43 = lean_ctor_get(x_42, 0);
x_81 = !lean_is_exclusive(x_42);
if (x_81 == 0)
{
x_44 = x_42;
x_45 = x_81;
goto block_80;
}
else
{
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = x_81;
goto block_80;
}
block_80:
{
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_46; lean_object* x_47; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_46 = lean_ctor_get_uint8(x_43, 0);
lean_dec_ref(x_43);
if (x_41 == 0)
{
x_47 = x_40;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_39);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_46);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_47);
x_48 = x_44;
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
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; uint8_t x_79; 
lean_del_object(x_44);
lean_del_object(x_40);
x_53 = lean_ctor_get(x_43, 0);
x_54 = lean_ctor_get(x_43, 1);
x_55 = lean_ctor_get_uint8(x_43, sizeof(void*)*2);
x_79 = !lean_is_exclusive(x_43);
if (x_79 == 0)
{
x_56 = x_43;
x_57 = x_79;
goto block_78;
}
else
{
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_43);
x_56 = lean_box(0);
x_57 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_58; 
lean_inc_ref(x_53);
x_58 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_38, x_39, x_53, x_54, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_69; 
x_59 = lean_ctor_get(x_58, 0);
x_69 = !lean_is_exclusive(x_58);
if (x_69 == 0)
{
x_60 = x_58;
x_61 = x_69;
goto block_68;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_62; 
if (x_57 == 0)
{
lean_ctor_set(x_56, 1, x_59);
x_62 = x_56;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_55);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_62);
x_63 = x_60;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
lean_del_object(x_56);
lean_dec_ref(x_53);
x_70 = lean_ctor_get(x_58, 0);
x_77 = !lean_is_exclusive(x_58);
if (x_77 == 0)
{
x_71 = x_58;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_58);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_70);
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
}
}
}
else
{
lean_del_object(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
x_12 = x_42;
goto block_16;
}
}
}
else
{
lean_dec_ref(x_34);
lean_dec(x_22);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = x_33;
goto block_16;
}
}
}
else
{
lean_dec(x_22);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = x_33;
goto block_16;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_84 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_84);
x_85 = x_25;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_84);
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
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_90 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
block_16:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_13, 0);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_12);
x_15 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_15;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpIteCbv___lam__0___closed__1));
x_15 = lean_name_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__1));
x_17 = lean_name_eq(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1));
x_19 = lean_name_eq(x_13, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__3));
x_21 = lean_name_eq(x_13, x_20);
lean_dec(x_13);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatcher(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4, &l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_simpControlCbv___closed__4);
x_24 = lean_box(x_19);
x_25 = lean_array_push(x_23, x_24);
x_26 = lean_box(x_19);
x_27 = lean_array_push(x_25, x_26);
x_28 = lean_box(x_21);
x_29 = lean_array_push(x_27, x_28);
x_30 = lean_box(x_21);
x_31 = lean_array_push(x_29, x_30);
x_32 = lean_box(x_21);
x_33 = lean_array_push(x_31, x_32);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
x_34 = l_Lean_Meta_Sym_Simp_simpInterlaced(x_1, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_35, 0);
lean_dec_ref(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec_ref(x_34);
x_37 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_37;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_34;
}
}
else
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_84; 
lean_dec_ref(x_34);
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
x_84 = !lean_is_exclusive(x_35);
if (x_84 == 0)
{
x_41 = x_35;
x_42 = x_84;
goto block_83;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_box(0);
x_42 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_43; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_39);
x_43 = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg(x_39, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_82; 
x_44 = lean_ctor_get(x_43, 0);
x_82 = !lean_is_exclusive(x_43);
if (x_82 == 0)
{
x_45 = x_43;
x_46 = x_82;
goto block_81;
}
else
{
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = x_82;
goto block_81;
}
block_81:
{
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_47; lean_object* x_48; 
lean_dec_ref(x_44);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_47 = 0;
if (x_42 == 0)
{
x_48 = x_41;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_40);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_47);
if (x_46 == 0)
{
lean_ctor_set(x_45, 0, x_48);
x_49 = x_45;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_80; 
lean_del_object(x_45);
lean_del_object(x_41);
x_54 = lean_ctor_get(x_44, 0);
x_55 = lean_ctor_get(x_44, 1);
x_80 = !lean_is_exclusive(x_44);
if (x_80 == 0)
{
x_56 = x_44;
x_57 = x_80;
goto block_79;
}
else
{
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_44);
x_56 = lean_box(0);
x_57 = x_80;
goto block_79;
}
block_79:
{
uint8_t x_58; lean_object* x_59; 
x_58 = 0;
lean_inc_ref(x_54);
x_59 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_1, x_39, x_40, x_54, x_55, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_70; 
x_60 = lean_ctor_get(x_59, 0);
x_70 = !lean_is_exclusive(x_59);
if (x_70 == 0)
{
x_61 = x_59;
x_62 = x_70;
goto block_69;
}
else
{
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_box(0);
x_62 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_63; 
if (x_57 == 0)
{
lean_ctor_set(x_56, 1, x_60);
x_63 = x_56;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_60);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_58);
if (x_62 == 0)
{
lean_ctor_set(x_61, 0, x_63);
x_64 = x_61;
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
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_del_object(x_56);
lean_dec_ref(x_54);
x_71 = lean_ctor_get(x_59, 0);
x_78 = !lean_is_exclusive(x_59);
if (x_78 == 0)
{
x_72 = x_59;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_59);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
}
}
}
else
{
lean_del_object(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_43;
}
}
}
else
{
lean_dec_ref(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_34;
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_34;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_13);
x_85 = l_Lean_Meta_Sym_Simp_simpDIteCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_13);
x_86 = l_Lean_Meta_Sym_Simp_simpCond(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_86;
}
}
else
{
lean_object* x_87; 
lean_dec(x_13);
x_87 = l_Lean_Meta_Sym_Simp_simpIteCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_88 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___redArg___closed__0));
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_simpControlCbv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_Cbv_simpControlCbv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Sym_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SynthInstance(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Sym_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_Sym_Lemmas(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_Opaque(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
}
#ifdef __cplusplus
}
#endif
