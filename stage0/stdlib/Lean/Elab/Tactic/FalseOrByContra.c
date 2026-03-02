// Lean compiler output
// Module: Lean.Elab.Tactic.FalseOrByContra
// Imports: public import Lean.Elab.Tactic.Basic public import Lean.Meta.Tactic.Apply public import Lean.Meta.Tactic.Intro
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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0_value;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__0 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__0_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__1 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__2_value_aux_0),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 114, 54, 50, 40, 156, 62, 47)}};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__2 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__3 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__3_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Elab.Tactic.FalseOrByContra"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__4 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__4_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.MVarId.falseOrByContra"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__5 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__5_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected at most one sugoal"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__6 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__6_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_MVarId_falseOrByContra___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_falseOrByContra___closed__7;
static lean_once_cell_t l_Lean_MVarId_falseOrByContra___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_falseOrByContra___closed__8;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__9 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__9_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__10 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__10_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "byContradiction"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__11 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__11_value;
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__10_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__12_value_aux_0),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__11_value),LEAN_SCALAR_PTR_LITERAL(92, 114, 13, 107, 214, 89, 53, 175)}};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__12 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__12_value;
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__9_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__13_value_aux_0),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__11_value),LEAN_SCALAR_PTR_LITERAL(143, 54, 188, 55, 95, 58, 91, 50)}};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__13 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__13_value;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_once_cell_t l_Lean_MVarId_falseOrByContra___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_MVarId_falseOrByContra___closed__14;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__15 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__15_value;
lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__0 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__0_value;
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__1 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__1_value;
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__2 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__2_value;
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "falseOrByContra"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__3 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_0),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_1),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_2),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 186, 236, 85, 98, 241, 184, 126)}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__4 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value;
static const lean_closure_object l_Lean_MVarId_elabFalseOrByContra___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__5 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__5_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "MVarId"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value;
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabFalseOrByContra"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_0),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 186, 234, 138, 172, 166, 87, 74)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_1),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(16, 121, 168, 236, 1, 165, 84, 207)}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(62) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(64) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(62) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(62) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6_value;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0));
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_falseOrByContra___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__6));
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(66u);
x_4 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__5));
x_5 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_MVarId_falseOrByContra___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__6));
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_unsigned_to_nat(61u);
x_4 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__5));
x_5 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static uint64_t _init_l_Lean_MVarId_falseOrByContra___closed__14(void) {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 0;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_105; 
lean_inc(x_1);
x_105 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_107 = l_Lean_Meta_whnfR(x_106, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_299; 
x_108 = lean_ctor_get(x_107, 0);
x_299 = !lean_is_exclusive(x_107);
if (x_299 == 0)
{
x_109 = x_107;
x_110 = x_299;
goto block_298;
}
else
{
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_box(0);
x_110 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
switch (lean_obj_tag(x_108)) {
case 4:
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_108, 0);
if (lean_obj_tag(x_168) == 1)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_ctor_get(x_168, 1);
x_171 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__0));
x_172 = lean_string_dec_eq(x_170, x_171);
if (x_172 == 0)
{
lean_del_object(x_109);
x_111 = x_3;
x_112 = x_4;
x_113 = x_5;
x_114 = x_6;
goto block_167;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_108);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_1);
if (x_110 == 0)
{
lean_ctor_set(x_109, 0, x_173);
x_174 = x_109;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_173);
x_174 = x_176;
goto block_175;
}
block_175:
{
return x_174;
}
}
}
else
{
lean_del_object(x_109);
x_111 = x_3;
x_112 = x_4;
x_113 = x_5;
x_114 = x_6;
goto block_167;
}
}
else
{
lean_del_object(x_109);
x_111 = x_3;
x_112 = x_4;
x_113 = x_5;
x_114 = x_6;
goto block_167;
}
}
case 7:
{
lean_object* x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; lean_object* x_196; uint8_t x_197; uint8_t x_234; 
lean_dec_ref(x_108);
lean_del_object(x_109);
x_177 = l_Lean_Meta_Context_config(x_3);
x_178 = lean_ctor_get_uint8(x_177, 0);
x_179 = lean_ctor_get_uint8(x_177, 1);
x_180 = lean_ctor_get_uint8(x_177, 2);
x_181 = lean_ctor_get_uint8(x_177, 3);
x_182 = lean_ctor_get_uint8(x_177, 4);
x_183 = lean_ctor_get_uint8(x_177, 5);
x_184 = lean_ctor_get_uint8(x_177, 6);
x_185 = lean_ctor_get_uint8(x_177, 7);
x_186 = lean_ctor_get_uint8(x_177, 8);
x_187 = lean_ctor_get_uint8(x_177, 10);
x_188 = lean_ctor_get_uint8(x_177, 11);
x_189 = lean_ctor_get_uint8(x_177, 12);
x_190 = lean_ctor_get_uint8(x_177, 13);
x_191 = lean_ctor_get_uint8(x_177, 14);
x_192 = lean_ctor_get_uint8(x_177, 15);
x_193 = lean_ctor_get_uint8(x_177, 16);
x_194 = lean_ctor_get_uint8(x_177, 17);
x_195 = lean_ctor_get_uint8(x_177, 18);
x_234 = !lean_is_exclusive(x_177);
if (x_234 == 0)
{
x_196 = x_177;
x_197 = x_234;
goto block_233;
}
else
{
lean_dec(x_177);
x_196 = lean_box(0);
x_197 = x_234;
goto block_233;
}
block_233:
{
uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; lean_object* x_209; 
x_198 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_199 = lean_ctor_get(x_3, 1);
x_200 = lean_ctor_get(x_3, 2);
x_201 = lean_ctor_get(x_3, 3);
x_202 = lean_ctor_get(x_3, 4);
x_203 = lean_ctor_get(x_3, 5);
x_204 = lean_ctor_get(x_3, 6);
x_205 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_206 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
x_207 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 3);
x_208 = 0;
if (x_197 == 0)
{
x_209 = x_196;
goto block_231;
}
else
{
lean_object* x_232; 
x_232 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_232, 0, x_178);
lean_ctor_set_uint8(x_232, 1, x_179);
lean_ctor_set_uint8(x_232, 2, x_180);
lean_ctor_set_uint8(x_232, 3, x_181);
lean_ctor_set_uint8(x_232, 4, x_182);
lean_ctor_set_uint8(x_232, 5, x_183);
lean_ctor_set_uint8(x_232, 6, x_184);
lean_ctor_set_uint8(x_232, 7, x_185);
lean_ctor_set_uint8(x_232, 8, x_186);
lean_ctor_set_uint8(x_232, 10, x_187);
lean_ctor_set_uint8(x_232, 11, x_188);
lean_ctor_set_uint8(x_232, 12, x_189);
lean_ctor_set_uint8(x_232, 13, x_190);
lean_ctor_set_uint8(x_232, 14, x_191);
lean_ctor_set_uint8(x_232, 15, x_192);
lean_ctor_set_uint8(x_232, 16, x_193);
lean_ctor_set_uint8(x_232, 17, x_194);
lean_ctor_set_uint8(x_232, 18, x_195);
x_209 = x_232;
goto block_231;
}
block_231:
{
uint64_t x_210; uint64_t x_211; uint64_t x_212; uint64_t x_213; uint64_t x_214; uint64_t x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; 
lean_ctor_set_uint8(x_209, 9, x_208);
x_210 = l_Lean_Meta_Context_configKey(x_3);
x_211 = 2;
x_212 = lean_uint64_shift_right(x_210, x_211);
x_213 = lean_uint64_shift_left(x_212, x_211);
x_214 = lean_uint64_once(&l_Lean_MVarId_falseOrByContra___closed__14, &l_Lean_MVarId_falseOrByContra___closed__14_once, _init_l_Lean_MVarId_falseOrByContra___closed__14);
x_215 = lean_uint64_lor(x_213, x_214);
x_216 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_216, 0, x_209);
lean_ctor_set_uint64(x_216, sizeof(void*)*1, x_215);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc_ref(x_201);
lean_inc_ref(x_200);
lean_inc(x_199);
x_217 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_199);
lean_ctor_set(x_217, 2, x_200);
lean_ctor_set(x_217, 3, x_201);
lean_ctor_set(x_217, 4, x_202);
lean_ctor_set(x_217, 5, x_203);
lean_ctor_set(x_217, 6, x_204);
lean_ctor_set_uint8(x_217, sizeof(void*)*7, x_198);
lean_ctor_set_uint8(x_217, sizeof(void*)*7 + 1, x_205);
lean_ctor_set_uint8(x_217, sizeof(void*)*7 + 2, x_206);
lean_ctor_set_uint8(x_217, sizeof(void*)*7 + 3, x_207);
x_218 = 1;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_219 = l_Lean_Meta_intro1Core(x_1, x_218, x_217, x_4, x_5, x_6);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_1 = x_221;
goto _start;
}
else
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; uint8_t x_230; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_223 = lean_ctor_get(x_219, 0);
x_230 = !lean_is_exclusive(x_219);
if (x_230 == 0)
{
x_224 = x_219;
x_225 = x_230;
goto block_229;
}
else
{
lean_inc(x_223);
lean_dec(x_219);
x_224 = lean_box(0);
x_225 = x_230;
goto block_229;
}
block_229:
{
lean_object* x_226; 
if (x_225 == 0)
{
x_226 = x_224;
goto block_227;
}
else
{
lean_object* x_228; 
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_223);
x_226 = x_228;
goto block_227;
}
block_227:
{
return x_226;
}
}
}
}
}
}
case 5:
{
lean_object* x_235; 
lean_del_object(x_109);
x_235 = lean_ctor_get(x_108, 0);
if (lean_obj_tag(x_235) == 4)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_235, 0);
if (lean_obj_tag(x_236) == 1)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_236, 0);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_236, 1);
x_239 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__15));
x_240 = lean_string_dec_eq(x_238, x_239);
if (x_240 == 0)
{
x_111 = x_3;
x_112 = x_4;
x_113 = x_5;
x_114 = x_6;
goto block_167;
}
else
{
lean_object* x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; uint8_t x_253; uint8_t x_254; uint8_t x_255; uint8_t x_256; uint8_t x_257; uint8_t x_258; uint8_t x_259; lean_object* x_260; uint8_t x_261; uint8_t x_297; 
lean_dec_ref(x_108);
x_241 = l_Lean_Meta_Context_config(x_3);
x_242 = lean_ctor_get_uint8(x_241, 0);
x_243 = lean_ctor_get_uint8(x_241, 1);
x_244 = lean_ctor_get_uint8(x_241, 2);
x_245 = lean_ctor_get_uint8(x_241, 3);
x_246 = lean_ctor_get_uint8(x_241, 4);
x_247 = lean_ctor_get_uint8(x_241, 5);
x_248 = lean_ctor_get_uint8(x_241, 6);
x_249 = lean_ctor_get_uint8(x_241, 7);
x_250 = lean_ctor_get_uint8(x_241, 8);
x_251 = lean_ctor_get_uint8(x_241, 10);
x_252 = lean_ctor_get_uint8(x_241, 11);
x_253 = lean_ctor_get_uint8(x_241, 12);
x_254 = lean_ctor_get_uint8(x_241, 13);
x_255 = lean_ctor_get_uint8(x_241, 14);
x_256 = lean_ctor_get_uint8(x_241, 15);
x_257 = lean_ctor_get_uint8(x_241, 16);
x_258 = lean_ctor_get_uint8(x_241, 17);
x_259 = lean_ctor_get_uint8(x_241, 18);
x_297 = !lean_is_exclusive(x_241);
if (x_297 == 0)
{
x_260 = x_241;
x_261 = x_297;
goto block_296;
}
else
{
lean_dec(x_241);
x_260 = lean_box(0);
x_261 = x_297;
goto block_296;
}
block_296:
{
uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; lean_object* x_273; 
x_262 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_263 = lean_ctor_get(x_3, 1);
x_264 = lean_ctor_get(x_3, 2);
x_265 = lean_ctor_get(x_3, 3);
x_266 = lean_ctor_get(x_3, 4);
x_267 = lean_ctor_get(x_3, 5);
x_268 = lean_ctor_get(x_3, 6);
x_269 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_270 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
x_271 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 3);
x_272 = 0;
if (x_261 == 0)
{
x_273 = x_260;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_295, 0, x_242);
lean_ctor_set_uint8(x_295, 1, x_243);
lean_ctor_set_uint8(x_295, 2, x_244);
lean_ctor_set_uint8(x_295, 3, x_245);
lean_ctor_set_uint8(x_295, 4, x_246);
lean_ctor_set_uint8(x_295, 5, x_247);
lean_ctor_set_uint8(x_295, 6, x_248);
lean_ctor_set_uint8(x_295, 7, x_249);
lean_ctor_set_uint8(x_295, 8, x_250);
lean_ctor_set_uint8(x_295, 10, x_251);
lean_ctor_set_uint8(x_295, 11, x_252);
lean_ctor_set_uint8(x_295, 12, x_253);
lean_ctor_set_uint8(x_295, 13, x_254);
lean_ctor_set_uint8(x_295, 14, x_255);
lean_ctor_set_uint8(x_295, 15, x_256);
lean_ctor_set_uint8(x_295, 16, x_257);
lean_ctor_set_uint8(x_295, 17, x_258);
lean_ctor_set_uint8(x_295, 18, x_259);
x_273 = x_295;
goto block_294;
}
block_294:
{
uint64_t x_274; uint64_t x_275; uint64_t x_276; uint64_t x_277; uint64_t x_278; uint64_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_ctor_set_uint8(x_273, 9, x_272);
x_274 = l_Lean_Meta_Context_configKey(x_3);
x_275 = 2;
x_276 = lean_uint64_shift_right(x_274, x_275);
x_277 = lean_uint64_shift_left(x_276, x_275);
x_278 = lean_uint64_once(&l_Lean_MVarId_falseOrByContra___closed__14, &l_Lean_MVarId_falseOrByContra___closed__14_once, _init_l_Lean_MVarId_falseOrByContra___closed__14);
x_279 = lean_uint64_lor(x_277, x_278);
x_280 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_280, 0, x_273);
lean_ctor_set_uint64(x_280, sizeof(void*)*1, x_279);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc_ref(x_265);
lean_inc_ref(x_264);
lean_inc(x_263);
x_281 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_263);
lean_ctor_set(x_281, 2, x_264);
lean_ctor_set(x_281, 3, x_265);
lean_ctor_set(x_281, 4, x_266);
lean_ctor_set(x_281, 5, x_267);
lean_ctor_set(x_281, 6, x_268);
lean_ctor_set_uint8(x_281, sizeof(void*)*7, x_262);
lean_ctor_set_uint8(x_281, sizeof(void*)*7 + 1, x_269);
lean_ctor_set_uint8(x_281, sizeof(void*)*7 + 2, x_270);
lean_ctor_set_uint8(x_281, sizeof(void*)*7 + 3, x_271);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_282 = l_Lean_Meta_intro1Core(x_1, x_240, x_281, x_4, x_5, x_6);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
lean_dec_ref(x_282);
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec(x_283);
x_1 = x_284;
goto _start;
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; uint8_t x_293; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_286 = lean_ctor_get(x_282, 0);
x_293 = !lean_is_exclusive(x_282);
if (x_293 == 0)
{
x_287 = x_282;
x_288 = x_293;
goto block_292;
}
else
{
lean_inc(x_286);
lean_dec(x_282);
x_287 = lean_box(0);
x_288 = x_293;
goto block_292;
}
block_292:
{
lean_object* x_289; 
if (x_288 == 0)
{
x_289 = x_287;
goto block_290;
}
else
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_286);
x_289 = x_291;
goto block_290;
}
block_290:
{
return x_289;
}
}
}
}
}
}
}
else
{
x_111 = x_3;
x_112 = x_4;
x_113 = x_5;
x_114 = x_6;
goto block_167;
}
}
else
{
x_111 = x_3;
x_112 = x_4;
x_113 = x_5;
x_114 = x_6;
goto block_167;
}
}
else
{
x_111 = x_3;
x_112 = x_4;
x_113 = x_5;
x_114 = x_6;
goto block_167;
}
}
default: 
{
lean_del_object(x_109);
x_111 = x_3;
x_112 = x_4;
x_113 = x_5;
x_114 = x_6;
goto block_167;
}
}
block_167:
{
lean_object* x_115; 
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
x_115 = l_Lean_Meta_isProp(x_108, x_111, x_112, x_113, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
x_117 = lean_unbox(x_116);
if (x_117 == 0)
{
lean_dec(x_116);
x_12 = x_111;
x_13 = x_112;
x_14 = x_113;
x_15 = x_114;
x_16 = lean_box(0);
goto block_41;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; 
x_118 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__11));
x_119 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
x_120 = 0;
x_121 = 0;
x_122 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_122, 0, x_120);
x_123 = lean_unbox(x_116);
lean_ctor_set_uint8(x_122, 1, x_123);
lean_ctor_set_uint8(x_122, 2, x_121);
x_124 = lean_unbox(x_116);
lean_dec(x_116);
lean_ctor_set_uint8(x_122, 3, x_124);
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc_ref(x_122);
lean_inc(x_1);
x_125 = l_Lean_MVarId_applyConst(x_1, x_119, x_122, x_111, x_112, x_113, x_114);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
lean_dec_ref(x_122);
lean_dec(x_1);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_51 = x_126;
x_52 = x_111;
x_53 = x_112;
x_54 = x_113;
x_55 = x_114;
x_56 = lean_box(0);
goto block_81;
}
else
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec_ref(x_125);
x_128 = l_Lean_Exception_isInterrupt(x_127);
if (x_128 == 0)
{
uint8_t x_129; 
lean_inc(x_127);
x_129 = l_Lean_Exception_isRuntime(x_127);
x_82 = x_127;
x_83 = x_122;
x_84 = x_111;
x_85 = x_112;
x_86 = x_114;
x_87 = x_113;
x_88 = lean_box(0);
x_89 = x_118;
x_90 = x_129;
goto block_104;
}
else
{
x_82 = x_127;
x_83 = x_122;
x_84 = x_111;
x_85 = x_112;
x_86 = x_114;
x_87 = x_113;
x_88 = lean_box(0);
x_89 = x_118;
x_90 = x_128;
goto block_104;
}
}
}
else
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_2, 0);
x_131 = lean_unbox(x_130);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; lean_object* x_138; 
x_132 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
x_133 = 0;
x_134 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_134, 0, x_133);
x_135 = lean_unbox(x_116);
lean_ctor_set_uint8(x_134, 1, x_135);
x_136 = lean_unbox(x_130);
lean_ctor_set_uint8(x_134, 2, x_136);
x_137 = lean_unbox(x_116);
lean_dec(x_116);
lean_ctor_set_uint8(x_134, 3, x_137);
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc(x_1);
x_138 = l_Lean_MVarId_applyConst(x_1, x_132, x_134, x_111, x_112, x_113, x_114);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
lean_dec(x_1);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
x_51 = x_139;
x_52 = x_111;
x_53 = x_112;
x_54 = x_113;
x_55 = x_114;
x_56 = lean_box(0);
goto block_81;
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
lean_dec_ref(x_138);
x_141 = l_Lean_Exception_isInterrupt(x_140);
if (x_141 == 0)
{
uint8_t x_142; 
lean_inc(x_140);
x_142 = l_Lean_Exception_isRuntime(x_140);
x_42 = x_111;
x_43 = x_112;
x_44 = x_114;
x_45 = x_140;
x_46 = x_113;
x_47 = lean_box(0);
x_48 = x_142;
goto block_50;
}
else
{
x_42 = x_111;
x_43 = x_112;
x_44 = x_114;
x_45 = x_140;
x_46 = x_113;
x_47 = lean_box(0);
x_48 = x_141;
goto block_50;
}
}
}
else
{
lean_object* x_143; uint8_t x_144; uint8_t x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; 
x_143 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__13));
x_144 = 0;
x_145 = 0;
x_146 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_146, 0, x_144);
x_147 = lean_unbox(x_116);
lean_ctor_set_uint8(x_146, 1, x_147);
lean_ctor_set_uint8(x_146, 2, x_145);
x_148 = lean_unbox(x_116);
lean_dec(x_116);
lean_ctor_set_uint8(x_146, 3, x_148);
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
x_149 = l_Lean_MVarId_applyConst(x_1, x_143, x_146, x_111, x_112, x_113, x_114);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
x_51 = x_150;
x_52 = x_111;
x_53 = x_112;
x_54 = x_113;
x_55 = x_114;
x_56 = lean_box(0);
goto block_81;
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_158; 
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
x_151 = lean_ctor_get(x_149, 0);
x_158 = !lean_is_exclusive(x_149);
if (x_158 == 0)
{
x_152 = x_149;
x_153 = x_158;
goto block_157;
}
else
{
lean_inc(x_151);
lean_dec(x_149);
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
else
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_166; 
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_1);
x_159 = lean_ctor_get(x_115, 0);
x_166 = !lean_is_exclusive(x_115);
if (x_166 == 0)
{
x_160 = x_115;
x_161 = x_166;
goto block_165;
}
else
{
lean_inc(x_159);
lean_dec(x_115);
x_160 = lean_box(0);
x_161 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_162; 
if (x_161 == 0)
{
x_162 = x_160;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_159);
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
lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_307; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_300 = lean_ctor_get(x_107, 0);
x_307 = !lean_is_exclusive(x_107);
if (x_307 == 0)
{
x_301 = x_107;
x_302 = x_307;
goto block_306;
}
else
{
lean_inc(x_300);
lean_dec(x_107);
x_301 = lean_box(0);
x_302 = x_307;
goto block_306;
}
block_306:
{
lean_object* x_303; 
if (x_302 == 0)
{
x_303 = x_301;
goto block_304;
}
else
{
lean_object* x_305; 
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_300);
x_303 = x_305;
goto block_304;
}
block_304:
{
return x_303;
}
}
}
}
else
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_315; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_308 = lean_ctor_get(x_105, 0);
x_315 = !lean_is_exclusive(x_105);
if (x_315 == 0)
{
x_309 = x_105;
x_310 = x_315;
goto block_314;
}
else
{
lean_inc(x_308);
lean_dec(x_105);
x_309 = lean_box(0);
x_310 = x_315;
goto block_314;
}
block_314:
{
lean_object* x_311; 
if (x_310 == 0)
{
x_311 = x_309;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_308);
x_311 = x_313;
goto block_312;
}
block_312:
{
return x_311;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_41:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__2));
x_18 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__3));
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_19 = l_Lean_MVarId_applyConst(x_1, x_17, x_18, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_32; 
x_20 = lean_ctor_get(x_19, 0);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
x_21 = x_19;
x_22 = x_32;
goto block_31;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_32;
goto block_31;
}
block_31:
{
if (lean_obj_tag(x_20) == 0)
{
lean_del_object(x_21);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec_ref(x_20);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_25);
x_26 = x_21;
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
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_20);
lean_del_object(x_21);
x_29 = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__7, &l_Lean_MVarId_falseOrByContra___closed__7_once, _init_l_Lean_MVarId_falseOrByContra___closed__7);
x_30 = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(x_29, x_12, x_13, x_14, x_15);
return x_30;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_33 = lean_ctor_get(x_19, 0);
x_40 = !lean_is_exclusive(x_19);
if (x_40 == 0)
{
x_34 = x_19;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_19);
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
block_50:
{
if (x_48 == 0)
{
lean_dec_ref(x_45);
x_12 = x_42;
x_13 = x_43;
x_14 = x_46;
x_15 = x_44;
x_16 = lean_box(0);
goto block_41;
}
else
{
lean_object* x_49; 
lean_dec_ref(x_46);
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_1);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_45);
return x_49;
}
}
block_81:
{
if (lean_obj_tag(x_51) == 0)
{
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_51, 1);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec_ref(x_51);
x_59 = 0;
x_60 = l_Lean_Meta_intro1Core(x_58, x_59, x_52, x_53, x_54, x_55);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_70; 
x_61 = lean_ctor_get(x_60, 0);
x_70 = !lean_is_exclusive(x_60);
if (x_70 == 0)
{
x_62 = x_60;
x_63 = x_70;
goto block_69;
}
else
{
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_box(0);
x_63 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
if (x_63 == 0)
{
lean_ctor_set(x_62, 0, x_65);
x_66 = x_62;
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
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
x_71 = lean_ctor_get(x_60, 0);
x_78 = !lean_is_exclusive(x_60);
if (x_78 == 0)
{
x_72 = x_60;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_60);
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
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_51);
x_79 = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__8, &l_Lean_MVarId_falseOrByContra___closed__8_once, _init_l_Lean_MVarId_falseOrByContra___closed__8);
x_80 = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(x_79, x_52, x_53, x_54, x_55);
return x_80;
}
}
}
block_104:
{
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_82);
x_91 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__9));
x_92 = l_Lean_Name_mkStr2(x_91, x_89);
lean_inc(x_86);
lean_inc_ref(x_87);
lean_inc(x_85);
lean_inc_ref(x_84);
x_93 = l_Lean_MVarId_applyConst(x_1, x_92, x_83, x_84, x_85, x_87, x_86);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_51 = x_94;
x_52 = x_84;
x_53 = x_85;
x_54 = x_87;
x_55 = x_86;
x_56 = lean_box(0);
goto block_81;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_102; 
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
x_95 = lean_ctor_get(x_93, 0);
x_102 = !lean_is_exclusive(x_93);
if (x_102 == 0)
{
x_96 = x_93;
x_97 = x_102;
goto block_101;
}
else
{
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
else
{
lean_object* x_103; 
lean_dec_ref(x_89);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_83);
lean_dec(x_1);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_82);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_falseOrByContra(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_box(0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = l_Lean_MVarId_falseOrByContra(x_11, x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_17, x_2, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_19, x_2, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_21 = lean_ctor_get(x_13, 0);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
x_22 = x_13;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_13);
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
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_29 = lean_ctor_get(x_10, 0);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
x_30 = x_10;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_elabFalseOrByContra___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__5));
x_15 = l_Lean_Elab_Tactic_withMainContext___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_elabFalseOrByContra(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
x_4 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
x_5 = lean_alloc_closure((void*)(l_Lean_MVarId_elabFalseOrByContra___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
x_3 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
}
#ifdef __cplusplus
}
#endif
