// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.IntInstTesters
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value;
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_94; 
lean_inc_ref(x_1);
x_94 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_10);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = l_Lean_Expr_cleanupAnnotations(x_95);
x_97 = l_Lean_Expr_isApp(x_96);
if (x_97 == 0)
{
lean_dec_ref(x_96);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_96, 1);
lean_inc_ref(x_98);
x_99 = l_Lean_Expr_appFnCleanup___redArg(x_96);
x_100 = l_Lean_Expr_isApp(x_99);
if (x_100 == 0)
{
lean_dec_ref(x_99);
lean_dec_ref(x_98);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_99, 1);
lean_inc_ref(x_101);
x_102 = l_Lean_Expr_appFnCleanup___redArg(x_99);
x_103 = l_Lean_Expr_isApp(x_102);
if (x_103 == 0)
{
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_98);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_102, 1);
lean_inc_ref(x_104);
x_105 = l_Lean_Expr_appFnCleanup___redArg(x_102);
x_106 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2));
x_107 = l_Lean_Expr_isConstOf(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5));
x_109 = l_Lean_Expr_isConstOf(x_105, x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = l_Lean_Expr_isApp(x_105);
if (x_110 == 0)
{
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_101);
lean_dec_ref(x_98);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_111; uint8_t x_112; 
x_111 = l_Lean_Expr_appFnCleanup___redArg(x_105);
x_112 = l_Lean_Expr_isApp(x_111);
if (x_112 == 0)
{
lean_dec_ref(x_111);
lean_dec_ref(x_104);
lean_dec_ref(x_101);
lean_dec_ref(x_98);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_113; uint8_t x_114; 
x_113 = l_Lean_Expr_appFnCleanup___redArg(x_111);
x_114 = l_Lean_Expr_isApp(x_113);
if (x_114 == 0)
{
lean_dec_ref(x_113);
lean_dec_ref(x_104);
lean_dec_ref(x_101);
lean_dec_ref(x_98);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = l_Lean_Expr_appFnCleanup___redArg(x_113);
x_116 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8));
x_117 = l_Lean_Expr_isConstOf(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11));
x_119 = l_Lean_Expr_isConstOf(x_115, x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14));
x_121 = l_Lean_Expr_isConstOf(x_115, x_120);
lean_dec_ref(x_115);
if (x_121 == 0)
{
lean_dec_ref(x_104);
lean_dec_ref(x_101);
lean_dec_ref(x_98);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_122; 
x_122 = l_Lean_Meta_Structural_isInstHAddInt___redArg(x_104, x_10);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_dec_ref(x_101);
lean_dec_ref(x_98);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_125 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_126 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_101, x_125, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_98, x_125, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_137; 
x_129 = lean_ctor_get(x_128, 0);
x_137 = !lean_is_exclusive(x_128);
if (x_137 == 0)
{
x_130 = x_128;
x_131 = x_137;
goto block_136;
}
else
{
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_box(0);
x_131 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_129);
if (x_131 == 0)
{
lean_ctor_set(x_130, 0, x_132);
x_133 = x_130;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_132);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
else
{
lean_dec(x_127);
return x_128;
}
}
else
{
lean_dec_ref(x_98);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_126;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_145; 
lean_dec_ref(x_101);
lean_dec_ref(x_98);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_138 = lean_ctor_get(x_122, 0);
x_145 = !lean_is_exclusive(x_122);
if (x_145 == 0)
{
x_139 = x_122;
x_140 = x_145;
goto block_144;
}
else
{
lean_inc(x_138);
lean_dec(x_122);
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
}
else
{
lean_object* x_146; 
lean_dec_ref(x_115);
x_146 = l_Lean_Meta_Structural_isInstHSubInt___redArg(x_104, x_10);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_dec_ref(x_101);
lean_dec_ref(x_98);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_149 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_150 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_101, x_149, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_98, x_149, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_161; 
x_153 = lean_ctor_get(x_152, 0);
x_161 = !lean_is_exclusive(x_152);
if (x_161 == 0)
{
x_154 = x_152;
x_155 = x_161;
goto block_160;
}
else
{
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_box(0);
x_155 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_156, 0, x_151);
lean_ctor_set(x_156, 1, x_153);
if (x_155 == 0)
{
lean_ctor_set(x_154, 0, x_156);
x_157 = x_154;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_156);
x_157 = x_159;
goto block_158;
}
block_158:
{
return x_157;
}
}
}
else
{
lean_dec(x_151);
return x_152;
}
}
else
{
lean_dec_ref(x_98);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_150;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; uint8_t x_169; 
lean_dec_ref(x_101);
lean_dec_ref(x_98);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_162 = lean_ctor_get(x_146, 0);
x_169 = !lean_is_exclusive(x_146);
if (x_169 == 0)
{
x_163 = x_146;
x_164 = x_169;
goto block_168;
}
else
{
lean_inc(x_162);
lean_dec(x_146);
x_163 = lean_box(0);
x_164 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_165; 
if (x_164 == 0)
{
x_165 = x_163;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_162);
x_165 = x_167;
goto block_166;
}
block_166:
{
return x_165;
}
}
}
}
}
else
{
lean_object* x_170; 
lean_dec_ref(x_115);
x_170 = l_Lean_Meta_Structural_isInstHMulInt___redArg(x_104, x_10);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec_ref(x_170);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_dec_ref(x_101);
lean_dec_ref(x_98);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_173; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_101);
x_173 = l_Lean_Meta_getIntValue_x3f(x_101, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_175 = l_Lean_Meta_getIntValue_x3f(x_98, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_dec_ref(x_101);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec_ref(x_176);
x_178 = lean_unsigned_to_nat(0u);
x_179 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_101, x_178, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_188; 
x_180 = lean_ctor_get(x_179, 0);
x_188 = !lean_is_exclusive(x_179);
if (x_188 == 0)
{
x_181 = x_179;
x_182 = x_188;
goto block_187;
}
else
{
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_box(0);
x_182 = x_188;
goto block_187;
}
block_187:
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_177);
if (x_182 == 0)
{
lean_ctor_set(x_181, 0, x_183);
x_184 = x_181;
goto block_185;
}
else
{
lean_object* x_186; 
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_183);
x_184 = x_186;
goto block_185;
}
block_185:
{
return x_184;
}
}
}
else
{
lean_dec(x_177);
return x_179;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_196; 
lean_dec_ref(x_101);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_189 = lean_ctor_get(x_175, 0);
x_196 = !lean_is_exclusive(x_175);
if (x_196 == 0)
{
x_190 = x_175;
x_191 = x_196;
goto block_195;
}
else
{
lean_inc(x_189);
lean_dec(x_175);
x_190 = lean_box(0);
x_191 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_192; 
if (x_191 == 0)
{
x_192 = x_190;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_189);
x_192 = x_194;
goto block_193;
}
block_193:
{
return x_192;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec_ref(x_101);
lean_dec(x_2);
lean_dec_ref(x_1);
x_197 = lean_ctor_get(x_174, 0);
lean_inc(x_197);
lean_dec_ref(x_174);
x_198 = lean_unsigned_to_nat(0u);
x_199 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_98, x_198, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_208; 
x_200 = lean_ctor_get(x_199, 0);
x_208 = !lean_is_exclusive(x_199);
if (x_208 == 0)
{
x_201 = x_199;
x_202 = x_208;
goto block_207;
}
else
{
lean_inc(x_200);
lean_dec(x_199);
x_201 = lean_box(0);
x_202 = x_208;
goto block_207;
}
block_207:
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_203, 0, x_197);
lean_ctor_set(x_203, 1, x_200);
if (x_202 == 0)
{
lean_ctor_set(x_201, 0, x_203);
x_204 = x_201;
goto block_205;
}
else
{
lean_object* x_206; 
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_203);
x_204 = x_206;
goto block_205;
}
block_205:
{
return x_204;
}
}
}
else
{
lean_dec(x_197);
return x_199;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_216; 
lean_dec_ref(x_101);
lean_dec_ref(x_98);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_209 = lean_ctor_get(x_173, 0);
x_216 = !lean_is_exclusive(x_173);
if (x_216 == 0)
{
x_210 = x_173;
x_211 = x_216;
goto block_215;
}
else
{
lean_inc(x_209);
lean_dec(x_173);
x_210 = lean_box(0);
x_211 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_212; 
if (x_211 == 0)
{
x_212 = x_210;
goto block_213;
}
else
{
lean_object* x_214; 
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_209);
x_212 = x_214;
goto block_213;
}
block_213:
{
return x_212;
}
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; uint8_t x_224; 
lean_dec_ref(x_101);
lean_dec_ref(x_98);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_217 = lean_ctor_get(x_170, 0);
x_224 = !lean_is_exclusive(x_170);
if (x_224 == 0)
{
x_218 = x_170;
x_219 = x_224;
goto block_223;
}
else
{
lean_inc(x_217);
lean_dec(x_170);
x_218 = lean_box(0);
x_219 = x_224;
goto block_223;
}
block_223:
{
lean_object* x_220; 
if (x_219 == 0)
{
x_220 = x_218;
goto block_221;
}
else
{
lean_object* x_222; 
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_217);
x_220 = x_222;
goto block_221;
}
block_221:
{
return x_220;
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
lean_object* x_225; 
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_101);
lean_dec_ref(x_98);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_225 = l_Lean_Meta_getIntValue_x3f(x_1, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_241; 
x_226 = lean_ctor_get(x_225, 0);
x_241 = !lean_is_exclusive(x_225);
if (x_241 == 0)
{
x_227 = x_225;
x_228 = x_241;
goto block_240;
}
else
{
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_box(0);
x_228 = x_241;
goto block_240;
}
block_240:
{
if (lean_obj_tag(x_226) == 1)
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_239; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_229 = lean_ctor_get(x_226, 0);
x_239 = !lean_is_exclusive(x_226);
if (x_239 == 0)
{
x_230 = x_226;
x_231 = x_239;
goto block_238;
}
else
{
lean_inc(x_229);
lean_dec(x_226);
x_230 = lean_box(0);
x_231 = x_239;
goto block_238;
}
block_238:
{
lean_object* x_232; 
if (x_231 == 0)
{
lean_ctor_set_tag(x_230, 0);
x_232 = x_230;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_237, 0, x_229);
x_232 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_233; 
if (x_228 == 0)
{
lean_ctor_set(x_227, 0, x_232);
x_233 = x_227;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_232);
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
lean_del_object(x_227);
lean_dec(x_226);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_249; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_242 = lean_ctor_get(x_225, 0);
x_249 = !lean_is_exclusive(x_225);
if (x_249 == 0)
{
x_243 = x_225;
x_244 = x_249;
goto block_248;
}
else
{
lean_inc(x_242);
lean_dec(x_225);
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
else
{
lean_object* x_250; 
lean_dec_ref(x_105);
lean_dec_ref(x_104);
x_250 = l_Lean_Meta_Structural_isInstNegInt___redArg(x_101, x_10);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; uint8_t x_252; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
x_252 = lean_unbox(x_251);
lean_dec(x_251);
if (x_252 == 0)
{
lean_dec_ref(x_98);
x_14 = x_1;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_253 = lean_unsigned_to_nat(0u);
x_254 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_98, x_253, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_263; 
x_255 = lean_ctor_get(x_254, 0);
x_263 = !lean_is_exclusive(x_254);
if (x_263 == 0)
{
x_256 = x_254;
x_257 = x_263;
goto block_262;
}
else
{
lean_inc(x_255);
lean_dec(x_254);
x_256 = lean_box(0);
x_257 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_258, 0, x_255);
if (x_257 == 0)
{
lean_ctor_set(x_256, 0, x_258);
x_259 = x_256;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_258);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
else
{
return x_254;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_271; 
lean_dec_ref(x_98);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_264 = lean_ctor_get(x_250, 0);
x_271 = !lean_is_exclusive(x_250);
if (x_271 == 0)
{
x_265 = x_250;
x_266 = x_271;
goto block_270;
}
else
{
lean_inc(x_264);
lean_dec(x_250);
x_265 = lean_box(0);
x_266 = x_271;
goto block_270;
}
block_270:
{
lean_object* x_267; 
if (x_266 == 0)
{
x_267 = x_265;
goto block_268;
}
else
{
lean_object* x_269; 
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_264);
x_267 = x_269;
goto block_268;
}
block_268:
{
return x_267;
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
lean_object* x_272; lean_object* x_273; uint8_t x_274; uint8_t x_279; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_272 = lean_ctor_get(x_94, 0);
x_279 = !lean_is_exclusive(x_94);
if (x_279 == 0)
{
x_273 = x_94;
x_274 = x_279;
goto block_278;
}
else
{
lean_inc(x_272);
lean_dec(x_94);
x_273 = lean_box(0);
x_274 = x_279;
goto block_278;
}
block_278:
{
lean_object* x_275; 
if (x_274 == 0)
{
x_275 = x_273;
goto block_276;
}
else
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_272);
x_275 = x_277;
goto block_276;
}
block_276:
{
return x_275;
}
}
}
block_93:
{
lean_object* x_26; 
x_26 = l_Lean_Meta_Sym_shareCommon___redArg(x_14, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_27, x_15);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_27);
x_32 = lean_grind_internalize(x_27, x_2, x_31, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec_ref(x_32);
x_33 = lean_grind_cutsat_mk_var(x_27, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_42; 
x_34 = lean_ctor_get(x_33, 0);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
x_35 = x_33;
x_36 = x_42;
goto block_41;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_34);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_37);
x_38 = x_35;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
x_43 = lean_ctor_get(x_33, 0);
x_50 = !lean_is_exclusive(x_33);
if (x_50 == 0)
{
x_44 = x_33;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_33);
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
lean_dec(x_27);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_51 = lean_ctor_get(x_32, 0);
x_58 = !lean_is_exclusive(x_32);
if (x_58 == 0)
{
x_52 = x_32;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_32);
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
lean_object* x_59; 
lean_dec(x_2);
x_59 = lean_grind_cutsat_mk_var(x_27, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_68; 
x_60 = lean_ctor_get(x_59, 0);
x_68 = !lean_is_exclusive(x_59);
if (x_68 == 0)
{
x_61 = x_59;
x_62 = x_68;
goto block_67;
}
else
{
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_box(0);
x_62 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_60);
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
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_76; 
x_69 = lean_ctor_get(x_59, 0);
x_76 = !lean_is_exclusive(x_59);
if (x_76 == 0)
{
x_70 = x_59;
x_71 = x_76;
goto block_75;
}
else
{
lean_inc(x_69);
lean_dec(x_59);
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
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_77 = lean_ctor_get(x_28, 0);
x_84 = !lean_is_exclusive(x_28);
if (x_84 == 0)
{
x_78 = x_28;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_28);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_85 = lean_ctor_get(x_26, 0);
x_92 = !lean_is_exclusive(x_26);
if (x_92 == 0)
{
x_86 = x_26;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_26);
x_86 = lean_box(0);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_87 == 0)
{
x_88 = x_86;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
}
#ifdef __cplusplus
}
#endif
