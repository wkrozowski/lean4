// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.ShortCircuit
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic public import Std.Tactic.BVDecide.Normalize.BitVec
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "mul_beq_mul_short_circuit_right"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 40, 88, 243, 189, 216, 201, 25)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__1_value;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__5;
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__0;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mul_beq_mul_short_circuit_left"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(204, 153, 253, 100, 53, 72, 164, 67)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(105, 120, 51, 161, 199, 191, 75, 23)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(6, 181, 64, 73, 102, 44, 61, 193)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(53, 48, 36, 136, 58, 30, 220, 150)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10;
extern lean_object* l_Lean_Meta_simpGlobalConfig;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "shortCircuitPass"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(45, 197, 199, 240, 107, 41, 97, 28)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_10, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_11, 0);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
x_13 = x_11;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_22; 
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc_ref(x_4);
x_22 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_1, x_2, x_3, x_4, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__0));
x_25 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__1));
x_26 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_5);
lean_ctor_set_uint8(x_26, sizeof(void*)*1 + 1, x_6);
x_27 = l_Lean_Name_mkStr6(x_7, x_8, x_9, x_10, x_11, x_24);
x_28 = l_Lean_mkConst(x_27, x_12);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
x_29 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_23, x_26, x_28, x_4, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Meta_getSimpCongrTheorems___redArg(x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_15, 1);
x_34 = lean_unsigned_to_nat(2u);
x_35 = 0;
x_36 = lean_box(0);
lean_inc(x_33);
x_37 = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 1, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 2, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 3, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 4, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 5, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 6, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 7, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 8, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 9, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 10, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 11, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 12, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 13, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 14, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 15, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 16, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 17, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 18, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 19, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 20, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 21, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 22, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 23, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 24, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 25, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 26, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 27, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 28, x_6);
x_38 = l_Lean_Meta_Simp_mkContext___redArg(x_37, x_30, x_32, x_17, x_19, x_20);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
x_40 = l_Lean_Meta_getPropHyps(x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_mk_empty_array_with_capacity(x_13);
x_43 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3);
lean_inc(x_13);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_13);
x_45 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4);
x_46 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__5);
x_47 = 5;
lean_inc(x_13);
x_48 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_13);
lean_ctor_set(x_48, 3, x_13);
lean_ctor_set_usize(x_48, 4, x_47);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Meta_simpGoal(x_14, x_39, x_42, x_36, x_5, x_41, x_50, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_72; 
x_52 = lean_ctor_get(x_51, 0);
x_72 = !lean_is_exclusive(x_51);
if (x_72 == 0)
{
x_53 = x_51;
x_54 = x_72;
goto block_71;
}
else
{
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
if (lean_obj_tag(x_55) == 1)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_67; 
x_56 = lean_ctor_get(x_55, 0);
x_67 = !lean_is_exclusive(x_55);
if (x_67 == 0)
{
x_57 = x_55;
x_58 = x_67;
goto block_66;
}
else
{
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_59);
x_60 = x_57;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_59);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_54 == 0)
{
lean_ctor_set(x_53, 0, x_60);
x_61 = x_53;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_60);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
else
{
lean_object* x_68; 
lean_dec(x_55);
if (x_54 == 0)
{
lean_ctor_set(x_53, 0, x_36);
x_68 = x_53;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_36);
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
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
x_73 = lean_ctor_get(x_51, 0);
x_80 = !lean_is_exclusive(x_51);
if (x_80 == 0)
{
x_74 = x_51;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_51);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec(x_39);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_81 = lean_ctor_get(x_40, 0);
x_88 = !lean_is_exclusive(x_40);
if (x_88 == 0)
{
x_82 = x_40;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_40);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_89 = lean_ctor_get(x_38, 0);
x_96 = !lean_is_exclusive(x_38);
if (x_96 == 0)
{
x_90 = x_38;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_38);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_104; 
lean_dec(x_30);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_97 = lean_ctor_get(x_31, 0);
x_104 = !lean_is_exclusive(x_31);
if (x_104 == 0)
{
x_98 = x_31;
x_99 = x_104;
goto block_103;
}
else
{
lean_inc(x_97);
lean_dec(x_31);
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
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_112; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_105 = lean_ctor_get(x_29, 0);
x_112 = !lean_is_exclusive(x_29);
if (x_112 == 0)
{
x_106 = x_29;
x_107 = x_112;
goto block_111;
}
else
{
lean_inc(x_105);
lean_dec(x_29);
x_106 = lean_box(0);
x_107 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_108; 
if (x_107 == 0)
{
x_108 = x_106;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_105);
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
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_120; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
x_113 = lean_ctor_get(x_22, 0);
x_120 = !lean_is_exclusive(x_22);
if (x_120 == 0)
{
x_114 = x_22;
x_115 = x_120;
goto block_119;
}
else
{
lean_inc(x_113);
lean_dec(x_22);
x_114 = lean_box(0);
x_115 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_116; 
if (x_115 == 0)
{
x_116 = x_114;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_113);
x_116 = x_118;
goto block_117;
}
block_117:
{
return x_116;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_unbox(x_5);
x_23 = lean_unbox(x_6);
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0(x_1, x_2, x_3, x_4, x_22, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_16);
lean_dec_ref(x_15);
return x_24;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__0);
x_11 = 1;
x_12 = 0;
x_13 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__3));
x_14 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__4));
x_15 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__5));
x_16 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__6));
x_17 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__7));
x_18 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__8));
x_19 = lean_box(0);
x_20 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10);
x_21 = l_Lean_Meta_simpGlobalConfig;
x_22 = lean_box(x_11);
x_23 = lean_box(x_12);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___boxed), 21, 14);
lean_closure_set(x_24, 0, x_10);
lean_closure_set(x_24, 1, x_13);
lean_closure_set(x_24, 2, x_20);
lean_closure_set(x_24, 3, x_21);
lean_closure_set(x_24, 4, x_22);
lean_closure_set(x_24, 5, x_23);
lean_closure_set(x_24, 6, x_14);
lean_closure_set(x_24, 7, x_15);
lean_closure_set(x_24, 8, x_16);
lean_closure_set(x_24, 9, x_17);
lean_closure_set(x_24, 10, x_18);
lean_closure_set(x_24, 11, x_19);
lean_closure_set(x_24, 12, x_9);
lean_closure_set(x_24, 13, x_1);
x_25 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(x_1, x_24, x_2, x_3, x_4, x_5, x_6, x_7);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Normalize_BitVec(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(builtin);
}
#ifdef __cplusplus
}
#endif
