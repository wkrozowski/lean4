// Lean compiler output
// Module: Lean.Elab.ElabRules
// Imports: public import Lean.Elab.MacroArgUtil public import Lean.Elab.AuxDef public import Lean.Elab.Do.Basic
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
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__10;
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0_value;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "invalid elab_rules alternative, expected syntax node kind `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "invalid elab_rules alternative, unexpected syntax node kind `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabRules"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__4_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__5;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__4_value),LEAN_SCALAR_PTR_LITERAL(187, 124, 47, 85, 21, 141, 50, 117)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Term.TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__9;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "stx"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__15;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__14_value),LEAN_SCALAR_PTR_LITERAL(89, 124, 230, 186, 154, 11, 21, 78)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__16_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__17 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__19 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__20 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__21 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__22 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noErrorIfUnused"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__23 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__23_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_error_if_unused%"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__24 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__24_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "throwUnsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__25 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__26;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value),LEAN_SCALAR_PTR_LITERAL(225, 251, 194, 35, 13, 152, 147, 184)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__27 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__27_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__28;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__29 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__30 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__31 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__32 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__33;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Elab.Command.CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__34 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__34_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__35;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__36 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__36_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Elab.Do.DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__37 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__37_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__38;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__39 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__39_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__40 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__40_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cont"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__41 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__41_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__42;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__41_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 177, 147, 174, 255, 200, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__43 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__43_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Tactic.Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__44 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__44_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__45;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__46 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__46_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expectedType\?"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__47 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__47_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__48;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__47_value),LEAN_SCALAR_PTR_LITERAL(47, 72, 75, 114, 68, 52, 233, 214)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__49 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__49_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__50 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__50_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.Term.withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__51 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__51_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__52;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__53 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__53_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__54 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__54_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__54_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__55 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__55_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElem"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__56 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__56_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__56_value),LEAN_SCALAR_PTR_LITERAL(224, 169, 39, 82, 97, 101, 60, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__57 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__57_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__58 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__58_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__59;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "` does not support expected type specification"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__60 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__60_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__61;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doElem_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__62 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__62_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__62_value),LEAN_SCALAR_PTR_LITERAL(211, 179, 163, 70, 253, 44, 85, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__63 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__63_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__64 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__64_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__64_value),LEAN_SCALAR_PTR_LITERAL(226, 9, 43, 122, 104, 86, 206, 223)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__65 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__65_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__66 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__66_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__66_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__67 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__67_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__68 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__68_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__68_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__69 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__69_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__70 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__70_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__70_value),LEAN_SCALAR_PTR_LITERAL(232, 67, 39, 189, 45, 247, 54, 81)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__71 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__71_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unsupported syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__72 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__72_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__73;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "command_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__74 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__74_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__74_value),LEAN_SCALAR_PTR_LITERAL(7, 200, 102, 28, 219, 237, 42, 33)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__75 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__75_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "invalid elab_rules command, specify category using `elab_rules : <cat> ...`"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__76 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__76_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__77;
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "<="};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__3_value;
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* l_Array_mkArray5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elab_rules"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 70, 226, 250, 127, 121, 118, 247)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value;
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Command_elabElabRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_elabElabRules___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_elabElabRules___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__0_value;
static const lean_closure_object l_Lean_Elab_Command_elabElabRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_elabElabRules___lam__2___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__0_value)} };
static const lean_object* l_Lean_Elab_Command_elabElabRules___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__1_value;
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabElabRules"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 97, 52, 186, 206, 196, 221, 235)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1_value;
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1_value;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0_value;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1_value;
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17_value;
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0_value;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1_value;
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0_value;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`("};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elab"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 177, 45, 203, 60, 20, 245, 118)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElab___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElab___closed__7;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__9_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "precedence"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__11_value),LEAN_SCALAR_PTR_LITERAL(69, 243, 176, 51, 48, 112, 202, 160)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabTail"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value),LEAN_SCALAR_PTR_LITERAL(131, 240, 225, 71, 37, 75, 83, 37)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__16_value;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabElab"};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 235, 135, 254, 44, 234, 233, 9)}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
x_7 = x_5;
x_8 = x_14;
goto block_13;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_mkIdentFrom(x_6, x_1, x_2);
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_9);
x_10 = x_7;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
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
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
x_16 = x_5;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(x_1, x_5, x_3);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(x_1, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Lean_Environment_header(x_4);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0(void) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(x_1, x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Elab_Command_getRef___redArg(x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_40; 
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_13, 0);
lean_dec(x_41);
x_14 = x_13;
x_15 = x_40;
goto block_39;
}
else
{
lean_dec(x_13);
x_14 = lean_box(0);
x_15 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 5);
x_17 = l_Lean_SourceInfo_fromRef(x_12, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_38; 
x_38 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_6);
lean_dec_ref(x_38);
x_18 = lean_box(0);
goto block_37;
}
else
{
x_18 = lean_box(0);
goto block_37;
}
block_37:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4));
x_20 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7));
x_21 = lean_mk_syntax_ident(x_4);
x_22 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
lean_inc(x_17);
x_23 = l_Lean_Syntax_node1(x_17, x_22, x_10);
lean_inc(x_17);
x_24 = l_Lean_Syntax_node2(x_17, x_20, x_21, x_23);
x_25 = l_Lean_Syntax_node2(x_17, x_19, x_2, x_24);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__10, &l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__10_once, _init_l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__10);
x_27 = lean_array_push(x_26, x_25);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_27);
x_28 = x_14;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = l_Lean_Syntax_TSepArray_getElems___redArg(x_31);
x_33 = lean_array_push(x_32, x_25);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_33);
x_34 = x_14;
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
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_42 = lean_ctor_get(x_13, 0);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
x_43 = x_13;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_13);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_50 = lean_ctor_get(x_11, 0);
x_57 = !lean_is_exclusive(x_11);
if (x_57 == 0)
{
x_51 = x_11;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_11);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
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
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_4);
lean_dec(x_2);
x_58 = lean_ctor_get(x_9, 0);
x_65 = !lean_is_exclusive(x_9);
if (x_65 == 0)
{
x_59 = x_9;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_9);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_5 = x_2;
x_6 = x_26;
goto block_25;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_23; 
x_7 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_3, 1);
lean_dec(x_24);
x_8 = x_3;
x_9 = x_23;
goto block_22;
}
else
{
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_10);
lean_ctor_set(x_8, 0, x_1);
x_11 = x_8;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_10);
x_11 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_12);
lean_ctor_set(x_5, 0, x_11);
x_13 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_MessageData_ofSyntax(x_7);
x_15 = l_Lean_indentD(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_1 = x_16;
x_2 = x_4;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_instInhabitedScope_default;
x_8 = l_List_head_x21___redArg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_pp_macroStack;
x_11 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_30; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_14, 0);
lean_dec(x_31);
x_16 = x_14;
x_17 = x_30;
goto block_29;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_1);
x_19 = x_16;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_18);
x_19 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofSyntax(x_15);
x_23 = l_Lean_indentD(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(x_24, x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3);
x_4 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5);
x_3 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2);
x_12 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__6, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__6_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__6);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_7);
x_10 = l_Lean_Elab_getBetterRef(x_6, x_7);
lean_dec(x_6);
x_11 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(x_9, x_7, x_3);
x_12 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_13 = x_11;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_12);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_5, 0);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
x_22 = x_5;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_26; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
x_15 = lean_ctor_get(x_3, 8);
x_16 = lean_ctor_get(x_3, 9);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_3, 7);
lean_dec(x_27);
x_18 = x_3;
x_19 = x_26;
goto block_25;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
if (x_19 == 0)
{
lean_ctor_set(x_18, 7, x_20);
x_21 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 2, x_10);
lean_ctor_set(x_24, 3, x_11);
lean_ctor_set(x_24, 4, x_12);
lean_ctor_set(x_24, 5, x_13);
lean_ctor_set(x_24, 6, x_14);
lean_ctor_set(x_24, 7, x_20);
lean_ctor_set(x_24, 8, x_15);
lean_ctor_set(x_24, 9, x_16);
lean_ctor_set_uint8(x_24, sizeof(void*)*10, x_17);
x_21 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_22; 
x_22 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(x_2, x_21, x_4);
return x_22;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_28 = lean_ctor_get(x_6, 0);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
x_29 = x_6;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec_ref(x_5);
x_7 = lean_box(0);
x_8 = lean_array_uget_borrowed(x_2, x_4);
lean_inc(x_8);
x_9 = l_Lean_Syntax_getKind(x_8);
lean_inc(x_1);
x_10 = l_Lean_Elab_Command_checkRuleKind(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
lean_inc(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_8);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_41; uint8_t x_42; 
x_10 = lean_array_uget(x_4, x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_4, x_3, x_11);
x_41 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5));
lean_inc(x_10);
x_42 = l_Lean_Syntax_isOfKind(x_10, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_10);
x_43 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
x_20 = x_43;
goto block_30;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = l_Lean_Syntax_getArg(x_10, x_44);
lean_inc(x_45);
x_46 = l_Lean_Syntax_matchesNull(x_45, x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_45);
lean_dec(x_10);
x_47 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
x_20 = x_47;
goto block_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_123; 
x_48 = l_Lean_Syntax_getArg(x_45, x_11);
lean_dec(x_45);
x_49 = lean_unsigned_to_nat(3u);
x_50 = l_Lean_Syntax_getArg(x_10, x_49);
x_65 = l_Lean_Syntax_getArgs(x_48);
lean_dec(x_48);
x_66 = lean_box(0);
x_67 = lean_array_get(x_66, x_65, x_11);
x_123 = l_Lean_Syntax_isQuot(x_67);
if (x_123 == 0)
{
if (x_46 == 0)
{
lean_inc_ref(x_5);
x_68 = x_5;
x_69 = x_6;
x_70 = lean_box(0);
goto block_122;
}
else
{
lean_object* x_124; 
x_124 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
if (lean_obj_tag(x_124) == 0)
{
lean_dec_ref(x_124);
lean_inc_ref(x_5);
x_68 = x_5;
x_69 = x_6;
x_70 = lean_box(0);
goto block_122;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_132; 
lean_dec(x_67);
lean_dec_ref(x_65);
lean_dec(x_50);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec(x_1);
x_125 = lean_ctor_get(x_124, 0);
x_132 = !lean_is_exclusive(x_124);
if (x_132 == 0)
{
x_126 = x_124;
x_127 = x_132;
goto block_131;
}
else
{
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_box(0);
x_127 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_128; 
if (x_127 == 0)
{
x_128 = x_126;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
}
}
else
{
lean_inc_ref(x_5);
x_68 = x_5;
x_69 = x_6;
x_70 = lean_box(0);
goto block_122;
}
block_64:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_52);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_57 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
x_58 = l_Array_append___redArg(x_57, x_51);
lean_dec_ref(x_51);
lean_inc(x_52);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_58);
lean_inc(x_52);
x_60 = l_Lean_Syntax_node1(x_52, x_56, x_59);
x_61 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_52);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Syntax_node4(x_52, x_41, x_55, x_60, x_62, x_50);
x_13 = x_63;
x_14 = lean_box(0);
goto block_19;
}
block_122:
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_inc(x_67);
x_71 = l_Lean_Syntax_getQuotContent(x_67);
lean_inc(x_71);
x_72 = l_Lean_Syntax_getKind(x_71);
lean_inc(x_1);
x_73 = l_Lean_Elab_Command_checkRuleKind(x_72, x_1);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10));
x_75 = lean_name_eq(x_72, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_67);
lean_dec_ref(x_65);
lean_dec(x_50);
x_76 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12);
x_77 = l_Lean_MessageData_ofName(x_72);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_10, x_80, x_68, x_69);
lean_dec(x_10);
x_20 = x_81;
goto block_30;
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_72);
x_82 = l_Lean_Syntax_getArgs(x_71);
lean_dec(x_71);
x_83 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
x_84 = lean_array_size(x_82);
x_85 = 0;
lean_inc(x_1);
x_86 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(x_1, x_82, x_84, x_85, x_83);
lean_dec_ref(x_82);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_dec(x_67);
lean_dec_ref(x_65);
lean_dec(x_50);
x_31 = lean_box(0);
x_32 = x_68;
x_33 = x_69;
goto block_40;
}
else
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_dec(x_67);
lean_dec_ref(x_65);
lean_dec(x_50);
x_31 = lean_box(0);
x_32 = x_68;
x_33 = x_69;
goto block_40;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_10);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = l_Lean_Elab_Command_getRef___redArg(x_68);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_68);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_92);
x_93 = lean_ctor_get(x_68, 5);
lean_inc(x_93);
lean_dec_ref(x_68);
x_94 = l_Lean_Syntax_setArg(x_67, x_44, x_89);
x_95 = lean_array_set(x_65, x_11, x_94);
x_96 = l_Lean_SourceInfo_fromRef(x_91, x_73);
lean_dec(x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_97; 
x_97 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_69);
if (lean_obj_tag(x_97) == 0)
{
lean_dec_ref(x_97);
x_51 = x_95;
x_52 = x_96;
x_53 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_50);
lean_dec_ref(x_12);
lean_dec_ref(x_5);
lean_dec(x_1);
x_98 = lean_ctor_get(x_97, 0);
x_105 = !lean_is_exclusive(x_97);
if (x_105 == 0)
{
x_99 = x_97;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
else
{
lean_dec_ref(x_93);
x_51 = x_95;
x_52 = x_96;
x_53 = lean_box(0);
goto block_64;
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_113; 
lean_dec(x_91);
lean_dec(x_89);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_65);
lean_dec(x_50);
lean_dec_ref(x_12);
lean_dec_ref(x_5);
lean_dec(x_1);
x_106 = lean_ctor_get(x_92, 0);
x_113 = !lean_is_exclusive(x_92);
if (x_113 == 0)
{
x_107 = x_92;
x_108 = x_113;
goto block_112;
}
else
{
lean_inc(x_106);
lean_dec(x_92);
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
lean_dec(x_89);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_65);
lean_dec(x_50);
lean_dec_ref(x_12);
lean_dec_ref(x_5);
lean_dec(x_1);
x_114 = lean_ctor_get(x_90, 0);
x_121 = !lean_is_exclusive(x_90);
if (x_121 == 0)
{
x_115 = x_90;
x_116 = x_121;
goto block_120;
}
else
{
lean_inc(x_114);
lean_dec(x_90);
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
}
}
}
else
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_65);
lean_dec(x_50);
x_13 = x_10;
x_14 = lean_box(0);
goto block_19;
}
}
}
}
block_19:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_array_uset(x_12, x_3, x_13);
x_3 = x_16;
x_4 = x_17;
goto _start;
}
block_30:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_13 = x_21;
x_14 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec_ref(x_12);
lean_dec_ref(x_5);
lean_dec(x_1);
x_22 = lean_ctor_get(x_20, 0);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
x_23 = x_20;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
block_40:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1);
lean_inc(x_1);
x_35 = l_Lean_MessageData_ofName(x_1);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_10, x_38, x_32, x_33);
lean_dec(x_10);
x_20 = x_39;
goto block_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec(x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__4));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__8));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__41));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__45(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__44));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__48(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__47));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__52(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__51));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__59(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__58));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__61(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__60));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__73(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__72));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__77(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__76));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_array_size(x_7);
x_12 = 0;
lean_inc_ref(x_8);
lean_inc(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(x_4, x_11, x_12, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_1032; 
x_14 = lean_ctor_get(x_13, 0);
x_1032 = !lean_is_exclusive(x_13);
if (x_1032 == 0)
{
x_15 = x_13;
x_16 = x_1032;
goto block_1031;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_1032;
goto block_1031;
}
block_1031:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_809; lean_object* x_810; lean_object* x_811; uint8_t x_812; lean_object* x_813; lean_object* x_814; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_1018; lean_object* x_1019; 
x_1018 = lean_ctor_get(x_5, 0);
x_1019 = l_Lean_TSyntax_getId(x_1018);
x_843 = x_1019;
x_844 = x_8;
x_845 = x_9;
x_846 = lean_box(0);
goto block_1017;
}
else
{
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_1020; 
x_1020 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__55));
x_843 = x_1020;
x_844 = x_8;
x_845 = x_9;
x_846 = lean_box(0);
goto block_1017;
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; uint8_t x_1025; uint8_t x_1030; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1021 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__77, &l_Lean_Elab_Command_elabElabRulesAux___closed__77_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__77);
x_1022 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(x_1021, x_8, x_9);
x_1023 = lean_ctor_get(x_1022, 0);
x_1030 = !lean_is_exclusive(x_1022);
if (x_1030 == 0)
{
x_1024 = x_1022;
x_1025 = x_1030;
goto block_1029;
}
else
{
lean_inc(x_1023);
lean_dec(x_1022);
x_1024 = lean_box(0);
x_1025 = x_1030;
goto block_1029;
}
block_1029:
{
lean_object* x_1026; 
if (x_1025 == 0)
{
x_1026 = x_1024;
goto block_1027;
}
else
{
lean_object* x_1028; 
x_1028 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1028, 0, x_1023);
x_1026 = x_1028;
goto block_1027;
}
block_1027:
{
return x_1026;
}
}
}
}
block_135:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_inc_ref(x_28);
x_30 = l_Array_append___redArg(x_28, x_29);
lean_dec_ref(x_29);
lean_inc(x_19);
lean_inc(x_24);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_30);
x_32 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_33 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_34 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_27);
x_35 = l_Lean_Name_mkStr4(x_27, x_32, x_33, x_34);
x_36 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_24);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_36);
x_38 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_39 = l_Lean_Syntax_SepArray_ofElems(x_38, x_26);
lean_dec_ref(x_26);
lean_inc_ref(x_28);
x_40 = l_Array_append___redArg(x_28, x_39);
lean_dec_ref(x_39);
lean_inc(x_19);
lean_inc(x_24);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_24);
lean_ctor_set(x_41, 1, x_19);
lean_ctor_set(x_41, 2, x_40);
x_42 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_24);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_24);
x_44 = l_Lean_Syntax_node3(x_24, x_35, x_37, x_41, x_43);
lean_inc(x_19);
lean_inc(x_24);
x_45 = l_Lean_Syntax_node1(x_24, x_19, x_44);
lean_inc(x_24);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_23);
x_47 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_48 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_18);
lean_inc(x_22);
x_49 = l_Lean_addMacroScope(x_22, x_48, x_18);
x_50 = lean_box(0);
lean_inc(x_24);
x_51 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_51, 0, x_24);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set(x_51, 3, x_50);
x_52 = lean_mk_syntax_ident(x_4);
lean_inc(x_19);
lean_inc(x_24);
x_53 = l_Lean_Syntax_node2(x_24, x_19, x_51, x_52);
x_54 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_24);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_24);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
x_57 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
lean_inc_ref(x_25);
lean_inc_ref(x_27);
x_58 = l_Lean_Name_mkStr4(x_27, x_25, x_33, x_57);
lean_inc(x_18);
lean_inc(x_58);
lean_inc(x_22);
x_59 = l_Lean_addMacroScope(x_22, x_58, x_18);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_50);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_50);
lean_inc(x_24);
x_62 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_62, 0, x_24);
lean_ctor_set(x_62, 1, x_56);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_61);
x_63 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_24);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_24);
lean_ctor_set(x_64, 1, x_63);
x_65 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_27);
x_66 = l_Lean_Name_mkStr4(x_27, x_32, x_33, x_65);
lean_inc(x_24);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_24);
lean_ctor_set(x_67, 1, x_65);
x_68 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(x_27);
x_69 = l_Lean_Name_mkStr4(x_27, x_32, x_33, x_68);
x_70 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
x_71 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(x_18);
lean_inc(x_22);
x_72 = l_Lean_addMacroScope(x_22, x_71, x_18);
lean_inc(x_24);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_24);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_50);
x_74 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_27);
x_75 = l_Lean_Name_mkStr4(x_27, x_32, x_33, x_74);
x_76 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_24);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_24);
lean_ctor_set(x_77, 1, x_76);
lean_inc(x_24);
x_78 = l_Lean_Syntax_node1(x_24, x_75, x_77);
lean_inc(x_78);
lean_inc_ref(x_73);
lean_inc(x_19);
lean_inc(x_24);
x_79 = l_Lean_Syntax_node2(x_24, x_19, x_73, x_78);
lean_inc_ref(x_28);
lean_inc(x_19);
lean_inc(x_24);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_24);
lean_ctor_set(x_80, 1, x_19);
lean_ctor_set(x_80, 2, x_28);
x_81 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_24);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_24);
lean_ctor_set(x_82, 1, x_81);
x_83 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(x_27);
x_84 = l_Lean_Name_mkStr4(x_27, x_32, x_33, x_83);
lean_inc(x_24);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_24);
lean_ctor_set(x_85, 1, x_83);
x_86 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(x_27);
x_87 = l_Lean_Name_mkStr4(x_27, x_32, x_33, x_86);
lean_inc_ref(x_80);
lean_inc(x_24);
x_88 = l_Lean_Syntax_node2(x_24, x_87, x_80, x_73);
lean_inc(x_19);
lean_inc(x_24);
x_89 = l_Lean_Syntax_node1(x_24, x_19, x_88);
x_90 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(x_24);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_24);
lean_ctor_set(x_91, 1, x_90);
x_92 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_27);
x_93 = l_Lean_Name_mkStr4(x_27, x_32, x_33, x_92);
x_94 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_27);
x_95 = l_Lean_Name_mkStr4(x_27, x_32, x_33, x_94);
x_96 = l_Array_append___redArg(x_28, x_14);
lean_dec(x_14);
x_97 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_24);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_24);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_19);
lean_inc(x_24);
x_99 = l_Lean_Syntax_node1(x_24, x_19, x_78);
lean_inc(x_19);
lean_inc(x_24);
x_100 = l_Lean_Syntax_node1(x_24, x_19, x_99);
x_101 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_27);
x_102 = l_Lean_Name_mkStr4(x_27, x_32, x_33, x_101);
x_103 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_24);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_24);
lean_ctor_set(x_104, 1, x_103);
x_105 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_106 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_107 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_108 = l_Lean_addMacroScope(x_22, x_107, x_18);
x_109 = l_Lean_Name_mkStr3(x_27, x_25, x_105);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_50);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_50);
lean_inc(x_24);
x_112 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_112, 0, x_24);
lean_ctor_set(x_112, 1, x_106);
lean_ctor_set(x_112, 2, x_108);
lean_ctor_set(x_112, 3, x_111);
lean_inc(x_24);
x_113 = l_Lean_Syntax_node2(x_24, x_102, x_104, x_112);
lean_inc_ref(x_82);
lean_inc(x_24);
x_114 = l_Lean_Syntax_node4(x_24, x_95, x_98, x_100, x_82, x_113);
x_115 = lean_array_push(x_96, x_114);
lean_inc(x_24);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_24);
lean_ctor_set(x_116, 1, x_19);
lean_ctor_set(x_116, 2, x_115);
lean_inc(x_24);
x_117 = l_Lean_Syntax_node1(x_24, x_93, x_116);
lean_inc_ref_n(x_80, 2);
lean_inc(x_24);
x_118 = l_Lean_Syntax_node6(x_24, x_84, x_85, x_80, x_80, x_89, x_91, x_117);
lean_inc(x_24);
x_119 = l_Lean_Syntax_node4(x_24, x_69, x_79, x_80, x_82, x_118);
lean_inc(x_24);
x_120 = l_Lean_Syntax_node2(x_24, x_66, x_67, x_119);
x_121 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__28, &l_Lean_Elab_Command_elabElabRulesAux___closed__28_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__28);
x_122 = lean_array_push(x_121, x_31);
x_123 = lean_array_push(x_122, x_45);
x_124 = lean_array_push(x_123, x_21);
x_125 = lean_array_push(x_124, x_46);
x_126 = lean_array_push(x_125, x_53);
x_127 = lean_array_push(x_126, x_55);
x_128 = lean_array_push(x_127, x_62);
x_129 = lean_array_push(x_128, x_64);
x_130 = lean_array_push(x_129, x_120);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_24);
lean_ctor_set(x_131, 1, x_20);
lean_ctor_set(x_131, 2, x_130);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_131);
x_132 = x_15;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_131);
x_132 = x_134;
goto block_133;
}
block_133:
{
return x_132;
}
}
block_151:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_143 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
x_144 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_145 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_146 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_147 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_1, 0);
lean_inc(x_148);
lean_dec_ref(x_1);
x_149 = l_Array_mkArray1___redArg(x_148);
x_17 = lean_box(0);
x_18 = x_136;
x_19 = x_146;
x_20 = x_145;
x_21 = x_138;
x_22 = x_140;
x_23 = x_144;
x_24 = x_137;
x_25 = x_143;
x_26 = x_139;
x_27 = x_142;
x_28 = x_147;
x_29 = x_149;
goto block_135;
}
else
{
lean_object* x_150; 
lean_dec(x_1);
x_150 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_17 = lean_box(0);
x_18 = x_136;
x_19 = x_146;
x_20 = x_145;
x_21 = x_138;
x_22 = x_140;
x_23 = x_144;
x_24 = x_137;
x_25 = x_143;
x_26 = x_139;
x_27 = x_142;
x_28 = x_147;
x_29 = x_150;
goto block_135;
}
}
block_250:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_inc_ref(x_163);
x_166 = l_Array_append___redArg(x_163, x_165);
lean_dec_ref(x_165);
lean_inc(x_157);
lean_inc(x_160);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_160);
lean_ctor_set(x_167, 1, x_157);
lean_ctor_set(x_167, 2, x_166);
x_168 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_169 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_170 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_154);
x_171 = l_Lean_Name_mkStr4(x_154, x_168, x_169, x_170);
x_172 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_160);
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_160);
lean_ctor_set(x_173, 1, x_172);
x_174 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_175 = l_Lean_Syntax_SepArray_ofElems(x_174, x_162);
lean_dec_ref(x_162);
lean_inc_ref(x_163);
x_176 = l_Array_append___redArg(x_163, x_175);
lean_dec_ref(x_175);
lean_inc(x_157);
lean_inc(x_160);
x_177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_177, 0, x_160);
lean_ctor_set(x_177, 1, x_157);
lean_ctor_set(x_177, 2, x_176);
x_178 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_160);
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_160);
lean_ctor_set(x_179, 1, x_178);
lean_inc(x_160);
x_180 = l_Lean_Syntax_node3(x_160, x_171, x_173, x_177, x_179);
lean_inc(x_157);
lean_inc(x_160);
x_181 = l_Lean_Syntax_node1(x_160, x_157, x_180);
lean_inc(x_160);
x_182 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_182, 0, x_160);
lean_ctor_set(x_182, 1, x_156);
x_183 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_184 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_158);
lean_inc(x_159);
x_185 = l_Lean_addMacroScope(x_159, x_184, x_158);
x_186 = lean_box(0);
lean_inc(x_160);
x_187 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_187, 0, x_160);
lean_ctor_set(x_187, 1, x_183);
lean_ctor_set(x_187, 2, x_185);
lean_ctor_set(x_187, 3, x_186);
x_188 = lean_mk_syntax_ident(x_4);
lean_inc(x_157);
lean_inc(x_160);
x_189 = l_Lean_Syntax_node2(x_160, x_157, x_187, x_188);
x_190 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_160);
x_191 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_191, 0, x_160);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__35, &l_Lean_Elab_Command_elabElabRulesAux___closed__35_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35);
x_193 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
lean_inc_ref(x_164);
lean_inc_ref(x_154);
x_194 = l_Lean_Name_mkStr4(x_154, x_164, x_152, x_193);
lean_inc(x_158);
lean_inc(x_194);
lean_inc(x_159);
x_195 = l_Lean_addMacroScope(x_159, x_194, x_158);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_186);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_186);
lean_inc(x_160);
x_198 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_198, 0, x_160);
lean_ctor_set(x_198, 1, x_192);
lean_ctor_set(x_198, 2, x_195);
lean_ctor_set(x_198, 3, x_197);
x_199 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_160);
x_200 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_200, 0, x_160);
lean_ctor_set(x_200, 1, x_199);
x_201 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_154);
x_202 = l_Lean_Name_mkStr4(x_154, x_168, x_169, x_201);
lean_inc(x_160);
x_203 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_203, 0, x_160);
lean_ctor_set(x_203, 1, x_201);
x_204 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_154);
x_205 = l_Lean_Name_mkStr4(x_154, x_168, x_169, x_204);
x_206 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_154);
x_207 = l_Lean_Name_mkStr4(x_154, x_168, x_169, x_206);
x_208 = l_Array_append___redArg(x_163, x_14);
lean_dec(x_14);
x_209 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_160);
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_160);
lean_ctor_set(x_210, 1, x_209);
x_211 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_154);
x_212 = l_Lean_Name_mkStr4(x_154, x_168, x_169, x_211);
x_213 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_160);
x_214 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_214, 0, x_160);
lean_ctor_set(x_214, 1, x_213);
lean_inc(x_160);
x_215 = l_Lean_Syntax_node1(x_160, x_212, x_214);
lean_inc(x_157);
lean_inc(x_160);
x_216 = l_Lean_Syntax_node1(x_160, x_157, x_215);
lean_inc(x_157);
lean_inc(x_160);
x_217 = l_Lean_Syntax_node1(x_160, x_157, x_216);
x_218 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_160);
x_219 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_219, 0, x_160);
lean_ctor_set(x_219, 1, x_218);
x_220 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_154);
x_221 = l_Lean_Name_mkStr4(x_154, x_168, x_169, x_220);
x_222 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_160);
x_223 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_223, 0, x_160);
lean_ctor_set(x_223, 1, x_222);
x_224 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_225 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_226 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_227 = l_Lean_addMacroScope(x_159, x_226, x_158);
x_228 = l_Lean_Name_mkStr3(x_154, x_164, x_224);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_186);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_186);
lean_inc(x_160);
x_231 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_231, 0, x_160);
lean_ctor_set(x_231, 1, x_225);
lean_ctor_set(x_231, 2, x_227);
lean_ctor_set(x_231, 3, x_230);
lean_inc(x_160);
x_232 = l_Lean_Syntax_node2(x_160, x_221, x_223, x_231);
lean_inc(x_160);
x_233 = l_Lean_Syntax_node4(x_160, x_207, x_210, x_217, x_219, x_232);
x_234 = lean_array_push(x_208, x_233);
lean_inc(x_160);
x_235 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_235, 0, x_160);
lean_ctor_set(x_235, 1, x_157);
lean_ctor_set(x_235, 2, x_234);
lean_inc(x_160);
x_236 = l_Lean_Syntax_node1(x_160, x_205, x_235);
lean_inc(x_160);
x_237 = l_Lean_Syntax_node2(x_160, x_202, x_203, x_236);
x_238 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__28, &l_Lean_Elab_Command_elabElabRulesAux___closed__28_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__28);
x_239 = lean_array_push(x_238, x_167);
x_240 = lean_array_push(x_239, x_181);
x_241 = lean_array_push(x_240, x_153);
x_242 = lean_array_push(x_241, x_182);
x_243 = lean_array_push(x_242, x_189);
x_244 = lean_array_push(x_243, x_191);
x_245 = lean_array_push(x_244, x_198);
x_246 = lean_array_push(x_245, x_200);
x_247 = lean_array_push(x_246, x_237);
x_248 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_248, 0, x_160);
lean_ctor_set(x_248, 1, x_161);
lean_ctor_set(x_248, 2, x_247);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
block_267:
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_257 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_258 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
x_259 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
x_260 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_261 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_262 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_263 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_1, 0);
lean_inc(x_264);
lean_dec_ref(x_1);
x_265 = l_Array_mkArray1___redArg(x_264);
x_152 = x_259;
x_153 = x_252;
x_154 = x_257;
x_155 = lean_box(0);
x_156 = x_260;
x_157 = x_262;
x_158 = x_254;
x_159 = x_255;
x_160 = x_251;
x_161 = x_261;
x_162 = x_253;
x_163 = x_263;
x_164 = x_258;
x_165 = x_265;
goto block_250;
}
else
{
lean_object* x_266; 
lean_dec(x_1);
x_266 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_152 = x_259;
x_153 = x_252;
x_154 = x_257;
x_155 = lean_box(0);
x_156 = x_260;
x_157 = x_262;
x_158 = x_254;
x_159 = x_255;
x_160 = x_251;
x_161 = x_261;
x_162 = x_253;
x_163 = x_263;
x_164 = x_258;
x_165 = x_266;
goto block_250;
}
}
block_389:
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_inc_ref(x_277);
x_281 = l_Array_append___redArg(x_277, x_280);
lean_dec_ref(x_280);
lean_inc(x_275);
lean_inc(x_272);
x_282 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_282, 0, x_272);
lean_ctor_set(x_282, 1, x_275);
lean_ctor_set(x_282, 2, x_281);
x_283 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_284 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_285 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_270);
x_286 = l_Lean_Name_mkStr4(x_270, x_283, x_284, x_285);
x_287 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_272);
x_288 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_288, 0, x_272);
lean_ctor_set(x_288, 1, x_287);
x_289 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_290 = l_Lean_Syntax_SepArray_ofElems(x_289, x_274);
lean_dec_ref(x_274);
lean_inc_ref(x_277);
x_291 = l_Array_append___redArg(x_277, x_290);
lean_dec_ref(x_290);
lean_inc(x_275);
lean_inc(x_272);
x_292 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_292, 0, x_272);
lean_ctor_set(x_292, 1, x_275);
lean_ctor_set(x_292, 2, x_291);
x_293 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_272);
x_294 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_294, 0, x_272);
lean_ctor_set(x_294, 1, x_293);
lean_inc(x_272);
x_295 = l_Lean_Syntax_node3(x_272, x_286, x_288, x_292, x_294);
lean_inc(x_275);
lean_inc(x_272);
x_296 = l_Lean_Syntax_node1(x_272, x_275, x_295);
lean_inc(x_272);
x_297 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_297, 0, x_272);
lean_ctor_set(x_297, 1, x_276);
x_298 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_299 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_268);
lean_inc(x_278);
x_300 = l_Lean_addMacroScope(x_278, x_299, x_268);
x_301 = lean_box(0);
lean_inc(x_272);
x_302 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_302, 0, x_272);
lean_ctor_set(x_302, 1, x_298);
lean_ctor_set(x_302, 2, x_300);
lean_ctor_set(x_302, 3, x_301);
x_303 = lean_mk_syntax_ident(x_4);
lean_inc(x_275);
lean_inc(x_272);
x_304 = l_Lean_Syntax_node2(x_272, x_275, x_302, x_303);
x_305 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_272);
x_306 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_306, 0, x_272);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__38, &l_Lean_Elab_Command_elabElabRulesAux___closed__38_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__38);
x_308 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
x_309 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
lean_inc_ref(x_279);
lean_inc_ref(x_270);
x_310 = l_Lean_Name_mkStr4(x_270, x_279, x_308, x_309);
lean_inc(x_268);
lean_inc(x_310);
lean_inc(x_278);
x_311 = l_Lean_addMacroScope(x_278, x_310, x_268);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_301);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_301);
lean_inc(x_272);
x_314 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_314, 0, x_272);
lean_ctor_set(x_314, 1, x_307);
lean_ctor_set(x_314, 2, x_311);
lean_ctor_set(x_314, 3, x_313);
x_315 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_272);
x_316 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_316, 0, x_272);
lean_ctor_set(x_316, 1, x_315);
x_317 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_270);
x_318 = l_Lean_Name_mkStr4(x_270, x_283, x_284, x_317);
lean_inc(x_272);
x_319 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_319, 0, x_272);
lean_ctor_set(x_319, 1, x_317);
x_320 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(x_270);
x_321 = l_Lean_Name_mkStr4(x_270, x_283, x_284, x_320);
x_322 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
x_323 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(x_268);
lean_inc(x_278);
x_324 = l_Lean_addMacroScope(x_278, x_323, x_268);
lean_inc(x_272);
x_325 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_325, 0, x_272);
lean_ctor_set(x_325, 1, x_322);
lean_ctor_set(x_325, 2, x_324);
lean_ctor_set(x_325, 3, x_301);
x_326 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__42, &l_Lean_Elab_Command_elabElabRulesAux___closed__42_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42);
x_327 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
lean_inc(x_268);
lean_inc(x_278);
x_328 = l_Lean_addMacroScope(x_278, x_327, x_268);
lean_inc(x_272);
x_329 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_329, 0, x_272);
lean_ctor_set(x_329, 1, x_326);
lean_ctor_set(x_329, 2, x_328);
lean_ctor_set(x_329, 3, x_301);
lean_inc_ref(x_325);
lean_inc(x_275);
lean_inc(x_272);
x_330 = l_Lean_Syntax_node2(x_272, x_275, x_325, x_329);
lean_inc_ref(x_277);
lean_inc(x_275);
lean_inc(x_272);
x_331 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_331, 0, x_272);
lean_ctor_set(x_331, 1, x_275);
lean_ctor_set(x_331, 2, x_277);
x_332 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_272);
x_333 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_333, 0, x_272);
lean_ctor_set(x_333, 1, x_332);
x_334 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(x_270);
x_335 = l_Lean_Name_mkStr4(x_270, x_283, x_284, x_334);
lean_inc(x_272);
x_336 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_336, 0, x_272);
lean_ctor_set(x_336, 1, x_334);
x_337 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(x_270);
x_338 = l_Lean_Name_mkStr4(x_270, x_283, x_284, x_337);
lean_inc_ref(x_331);
lean_inc(x_272);
x_339 = l_Lean_Syntax_node2(x_272, x_338, x_331, x_325);
lean_inc(x_275);
lean_inc(x_272);
x_340 = l_Lean_Syntax_node1(x_272, x_275, x_339);
x_341 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(x_272);
x_342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_342, 0, x_272);
lean_ctor_set(x_342, 1, x_341);
x_343 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_270);
x_344 = l_Lean_Name_mkStr4(x_270, x_283, x_284, x_343);
x_345 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_270);
x_346 = l_Lean_Name_mkStr4(x_270, x_283, x_284, x_345);
x_347 = l_Array_append___redArg(x_277, x_14);
lean_dec(x_14);
x_348 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_272);
x_349 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_349, 0, x_272);
lean_ctor_set(x_349, 1, x_348);
x_350 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_270);
x_351 = l_Lean_Name_mkStr4(x_270, x_283, x_284, x_350);
x_352 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_272);
x_353 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_353, 0, x_272);
lean_ctor_set(x_353, 1, x_352);
lean_inc(x_272);
x_354 = l_Lean_Syntax_node1(x_272, x_351, x_353);
lean_inc(x_275);
lean_inc(x_272);
x_355 = l_Lean_Syntax_node1(x_272, x_275, x_354);
lean_inc(x_275);
lean_inc(x_272);
x_356 = l_Lean_Syntax_node1(x_272, x_275, x_355);
x_357 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_270);
x_358 = l_Lean_Name_mkStr4(x_270, x_283, x_284, x_357);
x_359 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_272);
x_360 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_360, 0, x_272);
lean_ctor_set(x_360, 1, x_359);
x_361 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_362 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_363 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_364 = l_Lean_addMacroScope(x_278, x_363, x_268);
x_365 = l_Lean_Name_mkStr3(x_270, x_279, x_361);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_301);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_301);
lean_inc(x_272);
x_368 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_368, 0, x_272);
lean_ctor_set(x_368, 1, x_362);
lean_ctor_set(x_368, 2, x_364);
lean_ctor_set(x_368, 3, x_367);
lean_inc(x_272);
x_369 = l_Lean_Syntax_node2(x_272, x_358, x_360, x_368);
lean_inc_ref(x_333);
lean_inc(x_272);
x_370 = l_Lean_Syntax_node4(x_272, x_346, x_349, x_356, x_333, x_369);
x_371 = lean_array_push(x_347, x_370);
lean_inc(x_272);
x_372 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_372, 0, x_272);
lean_ctor_set(x_372, 1, x_275);
lean_ctor_set(x_372, 2, x_371);
lean_inc(x_272);
x_373 = l_Lean_Syntax_node1(x_272, x_344, x_372);
lean_inc_ref_n(x_331, 2);
lean_inc(x_272);
x_374 = l_Lean_Syntax_node6(x_272, x_335, x_336, x_331, x_331, x_340, x_342, x_373);
lean_inc(x_272);
x_375 = l_Lean_Syntax_node4(x_272, x_321, x_330, x_331, x_333, x_374);
lean_inc(x_272);
x_376 = l_Lean_Syntax_node2(x_272, x_318, x_319, x_375);
x_377 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__28, &l_Lean_Elab_Command_elabElabRulesAux___closed__28_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__28);
x_378 = lean_array_push(x_377, x_282);
x_379 = lean_array_push(x_378, x_296);
x_380 = lean_array_push(x_379, x_271);
x_381 = lean_array_push(x_380, x_297);
x_382 = lean_array_push(x_381, x_304);
x_383 = lean_array_push(x_382, x_306);
x_384 = lean_array_push(x_383, x_314);
x_385 = lean_array_push(x_384, x_316);
x_386 = lean_array_push(x_385, x_376);
x_387 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_387, 0, x_272);
lean_ctor_set(x_387, 1, x_269);
lean_ctor_set(x_387, 2, x_386);
x_388 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_388, 0, x_387);
return x_388;
}
block_405:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_396 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_397 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
x_398 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_399 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_400 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_401 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_ctor_get(x_1, 0);
lean_inc(x_402);
lean_dec_ref(x_1);
x_403 = l_Array_mkArray1___redArg(x_402);
x_268 = x_390;
x_269 = x_399;
x_270 = x_396;
x_271 = x_391;
x_272 = x_392;
x_273 = lean_box(0);
x_274 = x_393;
x_275 = x_400;
x_276 = x_398;
x_277 = x_401;
x_278 = x_394;
x_279 = x_397;
x_280 = x_403;
goto block_389;
}
else
{
lean_object* x_404; 
lean_dec(x_1);
x_404 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_268 = x_390;
x_269 = x_399;
x_270 = x_396;
x_271 = x_391;
x_272 = x_392;
x_273 = lean_box(0);
x_274 = x_393;
x_275 = x_400;
x_276 = x_398;
x_277 = x_401;
x_278 = x_394;
x_279 = x_397;
x_280 = x_404;
goto block_389;
}
}
block_503:
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_inc_ref(x_406);
x_419 = l_Array_append___redArg(x_406, x_418);
lean_dec_ref(x_418);
lean_inc(x_416);
lean_inc(x_412);
x_420 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_420, 0, x_412);
lean_ctor_set(x_420, 1, x_416);
lean_ctor_set(x_420, 2, x_419);
x_421 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_422 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_423 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_413);
x_424 = l_Lean_Name_mkStr4(x_413, x_421, x_422, x_423);
x_425 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_412);
x_426 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_426, 0, x_412);
lean_ctor_set(x_426, 1, x_425);
x_427 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_428 = l_Lean_Syntax_SepArray_ofElems(x_427, x_414);
lean_dec_ref(x_414);
lean_inc_ref(x_406);
x_429 = l_Array_append___redArg(x_406, x_428);
lean_dec_ref(x_428);
lean_inc(x_416);
lean_inc(x_412);
x_430 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_430, 0, x_412);
lean_ctor_set(x_430, 1, x_416);
lean_ctor_set(x_430, 2, x_429);
x_431 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_412);
x_432 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_432, 0, x_412);
lean_ctor_set(x_432, 1, x_431);
lean_inc(x_412);
x_433 = l_Lean_Syntax_node3(x_412, x_424, x_426, x_430, x_432);
lean_inc(x_416);
lean_inc(x_412);
x_434 = l_Lean_Syntax_node1(x_412, x_416, x_433);
lean_inc(x_412);
x_435 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_435, 0, x_412);
lean_ctor_set(x_435, 1, x_411);
x_436 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_437 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_417);
lean_inc(x_415);
x_438 = l_Lean_addMacroScope(x_415, x_437, x_417);
x_439 = lean_box(0);
lean_inc(x_412);
x_440 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_440, 0, x_412);
lean_ctor_set(x_440, 1, x_436);
lean_ctor_set(x_440, 2, x_438);
lean_ctor_set(x_440, 3, x_439);
x_441 = lean_mk_syntax_ident(x_4);
lean_inc(x_416);
lean_inc(x_412);
x_442 = l_Lean_Syntax_node2(x_412, x_416, x_440, x_441);
x_443 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_412);
x_444 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_444, 0, x_412);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__45, &l_Lean_Elab_Command_elabElabRulesAux___closed__45_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__45);
x_446 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__46));
lean_inc_ref(x_410);
lean_inc_ref(x_413);
x_447 = l_Lean_Name_mkStr4(x_413, x_410, x_446, x_446);
lean_inc(x_417);
lean_inc(x_447);
lean_inc(x_415);
x_448 = l_Lean_addMacroScope(x_415, x_447, x_417);
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_439);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_439);
lean_inc(x_412);
x_451 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_451, 0, x_412);
lean_ctor_set(x_451, 1, x_445);
lean_ctor_set(x_451, 2, x_448);
lean_ctor_set(x_451, 3, x_450);
x_452 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_412);
x_453 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_453, 0, x_412);
lean_ctor_set(x_453, 1, x_452);
x_454 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_413);
x_455 = l_Lean_Name_mkStr4(x_413, x_421, x_422, x_454);
lean_inc(x_412);
x_456 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_456, 0, x_412);
lean_ctor_set(x_456, 1, x_454);
x_457 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_413);
x_458 = l_Lean_Name_mkStr4(x_413, x_421, x_422, x_457);
x_459 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_413);
x_460 = l_Lean_Name_mkStr4(x_413, x_421, x_422, x_459);
x_461 = l_Array_append___redArg(x_406, x_14);
lean_dec(x_14);
x_462 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_412);
x_463 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_463, 0, x_412);
lean_ctor_set(x_463, 1, x_462);
x_464 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_413);
x_465 = l_Lean_Name_mkStr4(x_413, x_421, x_422, x_464);
x_466 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_412);
x_467 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_467, 0, x_412);
lean_ctor_set(x_467, 1, x_466);
lean_inc(x_412);
x_468 = l_Lean_Syntax_node1(x_412, x_465, x_467);
lean_inc(x_416);
lean_inc(x_412);
x_469 = l_Lean_Syntax_node1(x_412, x_416, x_468);
lean_inc(x_416);
lean_inc(x_412);
x_470 = l_Lean_Syntax_node1(x_412, x_416, x_469);
x_471 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_412);
x_472 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_472, 0, x_412);
lean_ctor_set(x_472, 1, x_471);
x_473 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_413);
x_474 = l_Lean_Name_mkStr4(x_413, x_421, x_422, x_473);
x_475 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_412);
x_476 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_476, 0, x_412);
lean_ctor_set(x_476, 1, x_475);
x_477 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_478 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_479 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_480 = l_Lean_addMacroScope(x_415, x_479, x_417);
x_481 = l_Lean_Name_mkStr3(x_413, x_410, x_477);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_439);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_439);
lean_inc(x_412);
x_484 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_484, 0, x_412);
lean_ctor_set(x_484, 1, x_478);
lean_ctor_set(x_484, 2, x_480);
lean_ctor_set(x_484, 3, x_483);
lean_inc(x_412);
x_485 = l_Lean_Syntax_node2(x_412, x_474, x_476, x_484);
lean_inc(x_412);
x_486 = l_Lean_Syntax_node4(x_412, x_460, x_463, x_470, x_472, x_485);
x_487 = lean_array_push(x_461, x_486);
lean_inc(x_412);
x_488 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_488, 0, x_412);
lean_ctor_set(x_488, 1, x_416);
lean_ctor_set(x_488, 2, x_487);
lean_inc(x_412);
x_489 = l_Lean_Syntax_node1(x_412, x_458, x_488);
lean_inc(x_412);
x_490 = l_Lean_Syntax_node2(x_412, x_455, x_456, x_489);
x_491 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__28, &l_Lean_Elab_Command_elabElabRulesAux___closed__28_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__28);
x_492 = lean_array_push(x_491, x_420);
x_493 = lean_array_push(x_492, x_434);
x_494 = lean_array_push(x_493, x_409);
x_495 = lean_array_push(x_494, x_435);
x_496 = lean_array_push(x_495, x_442);
x_497 = lean_array_push(x_496, x_444);
x_498 = lean_array_push(x_497, x_451);
x_499 = lean_array_push(x_498, x_453);
x_500 = lean_array_push(x_499, x_490);
x_501 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_501, 0, x_412);
lean_ctor_set(x_501, 1, x_408);
lean_ctor_set(x_501, 2, x_500);
x_502 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_502, 0, x_501);
return x_502;
}
block_519:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_510 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_511 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
x_512 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_513 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_514 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_515 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_516; lean_object* x_517; 
x_516 = lean_ctor_get(x_1, 0);
lean_inc(x_516);
lean_dec_ref(x_1);
x_517 = l_Array_mkArray1___redArg(x_516);
x_406 = x_515;
x_407 = lean_box(0);
x_408 = x_513;
x_409 = x_504;
x_410 = x_511;
x_411 = x_512;
x_412 = x_505;
x_413 = x_510;
x_414 = x_506;
x_415 = x_508;
x_416 = x_514;
x_417 = x_507;
x_418 = x_517;
goto block_503;
}
else
{
lean_object* x_518; 
lean_dec(x_1);
x_518 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_406 = x_515;
x_407 = lean_box(0);
x_408 = x_513;
x_409 = x_504;
x_410 = x_511;
x_411 = x_512;
x_412 = x_505;
x_413 = x_510;
x_414 = x_506;
x_415 = x_508;
x_416 = x_514;
x_417 = x_507;
x_418 = x_518;
goto block_503;
}
}
block_655:
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
lean_inc_ref(x_529);
x_534 = l_Array_append___redArg(x_529, x_533);
lean_dec_ref(x_533);
lean_inc(x_521);
lean_inc(x_526);
x_535 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_535, 0, x_526);
lean_ctor_set(x_535, 1, x_521);
lean_ctor_set(x_535, 2, x_534);
x_536 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_537 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_538 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_523);
x_539 = l_Lean_Name_mkStr4(x_523, x_536, x_537, x_538);
x_540 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_526);
x_541 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_541, 0, x_526);
lean_ctor_set(x_541, 1, x_540);
x_542 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_543 = l_Lean_Syntax_SepArray_ofElems(x_542, x_531);
lean_dec_ref(x_531);
lean_inc_ref(x_529);
x_544 = l_Array_append___redArg(x_529, x_543);
lean_dec_ref(x_543);
lean_inc(x_521);
lean_inc(x_526);
x_545 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_545, 0, x_526);
lean_ctor_set(x_545, 1, x_521);
lean_ctor_set(x_545, 2, x_544);
x_546 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_526);
x_547 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_547, 0, x_526);
lean_ctor_set(x_547, 1, x_546);
lean_inc(x_526);
x_548 = l_Lean_Syntax_node3(x_526, x_539, x_541, x_545, x_547);
lean_inc(x_521);
lean_inc(x_526);
x_549 = l_Lean_Syntax_node1(x_526, x_521, x_548);
lean_inc(x_526);
x_550 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_550, 0, x_526);
lean_ctor_set(x_550, 1, x_530);
x_551 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_552 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_527);
lean_inc(x_524);
x_553 = l_Lean_addMacroScope(x_524, x_552, x_527);
x_554 = lean_box(0);
lean_inc(x_526);
x_555 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_555, 0, x_526);
lean_ctor_set(x_555, 1, x_551);
lean_ctor_set(x_555, 2, x_553);
lean_ctor_set(x_555, 3, x_554);
x_556 = lean_mk_syntax_ident(x_4);
lean_inc(x_521);
lean_inc(x_526);
x_557 = l_Lean_Syntax_node2(x_526, x_521, x_555, x_556);
x_558 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_526);
x_559 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_559, 0, x_526);
lean_ctor_set(x_559, 1, x_558);
x_560 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
x_561 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
lean_inc_ref(x_528);
lean_inc_ref(x_523);
x_562 = l_Lean_Name_mkStr4(x_523, x_528, x_537, x_561);
lean_inc(x_527);
lean_inc(x_562);
lean_inc(x_524);
x_563 = l_Lean_addMacroScope(x_524, x_562, x_527);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_554);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_554);
lean_inc(x_526);
x_566 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_566, 0, x_526);
lean_ctor_set(x_566, 1, x_560);
lean_ctor_set(x_566, 2, x_563);
lean_ctor_set(x_566, 3, x_565);
x_567 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_526);
x_568 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_568, 0, x_526);
lean_ctor_set(x_568, 1, x_567);
x_569 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_523);
x_570 = l_Lean_Name_mkStr4(x_523, x_536, x_537, x_569);
lean_inc(x_526);
x_571 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_571, 0, x_526);
lean_ctor_set(x_571, 1, x_569);
x_572 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(x_523);
x_573 = l_Lean_Name_mkStr4(x_523, x_536, x_537, x_572);
x_574 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
x_575 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(x_527);
lean_inc(x_524);
x_576 = l_Lean_addMacroScope(x_524, x_575, x_527);
lean_inc(x_526);
x_577 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_577, 0, x_526);
lean_ctor_set(x_577, 1, x_574);
lean_ctor_set(x_577, 2, x_576);
lean_ctor_set(x_577, 3, x_554);
x_578 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__48, &l_Lean_Elab_Command_elabElabRulesAux___closed__48_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__48);
x_579 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__49));
lean_inc(x_527);
lean_inc(x_524);
x_580 = l_Lean_addMacroScope(x_524, x_579, x_527);
lean_inc(x_526);
x_581 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_581, 0, x_526);
lean_ctor_set(x_581, 1, x_578);
lean_ctor_set(x_581, 2, x_580);
lean_ctor_set(x_581, 3, x_554);
lean_inc_ref(x_581);
lean_inc_ref(x_577);
lean_inc(x_521);
lean_inc(x_526);
x_582 = l_Lean_Syntax_node2(x_526, x_521, x_577, x_581);
lean_inc_ref(x_529);
lean_inc(x_521);
lean_inc(x_526);
x_583 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_583, 0, x_526);
lean_ctor_set(x_583, 1, x_521);
lean_ctor_set(x_583, 2, x_529);
x_584 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_526);
x_585 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_585, 0, x_526);
lean_ctor_set(x_585, 1, x_584);
x_586 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__50));
lean_inc_ref(x_523);
x_587 = l_Lean_Name_mkStr4(x_523, x_536, x_537, x_586);
x_588 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__52, &l_Lean_Elab_Command_elabElabRulesAux___closed__52_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__52);
x_589 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__53));
lean_inc_ref(x_528);
lean_inc_ref(x_523);
x_590 = l_Lean_Name_mkStr4(x_523, x_528, x_537, x_589);
lean_inc(x_527);
lean_inc(x_590);
lean_inc(x_524);
x_591 = l_Lean_addMacroScope(x_524, x_590, x_527);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_554);
x_593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_554);
lean_inc(x_526);
x_594 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_594, 0, x_526);
lean_ctor_set(x_594, 1, x_588);
lean_ctor_set(x_594, 2, x_591);
lean_ctor_set(x_594, 3, x_593);
lean_inc(x_521);
lean_inc(x_526);
x_595 = l_Lean_Syntax_node1(x_526, x_521, x_525);
x_596 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(x_523);
x_597 = l_Lean_Name_mkStr4(x_523, x_536, x_537, x_596);
lean_inc(x_526);
x_598 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_598, 0, x_526);
lean_ctor_set(x_598, 1, x_596);
x_599 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(x_523);
x_600 = l_Lean_Name_mkStr4(x_523, x_536, x_537, x_599);
lean_inc_ref(x_583);
lean_inc(x_526);
x_601 = l_Lean_Syntax_node2(x_526, x_600, x_583, x_577);
lean_inc(x_521);
lean_inc(x_526);
x_602 = l_Lean_Syntax_node1(x_526, x_521, x_601);
x_603 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(x_526);
x_604 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_604, 0, x_526);
lean_ctor_set(x_604, 1, x_603);
x_605 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_523);
x_606 = l_Lean_Name_mkStr4(x_523, x_536, x_537, x_605);
x_607 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_523);
x_608 = l_Lean_Name_mkStr4(x_523, x_536, x_537, x_607);
x_609 = l_Array_append___redArg(x_529, x_14);
lean_dec(x_14);
x_610 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_526);
x_611 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_611, 0, x_526);
lean_ctor_set(x_611, 1, x_610);
x_612 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_523);
x_613 = l_Lean_Name_mkStr4(x_523, x_536, x_537, x_612);
x_614 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_526);
x_615 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_615, 0, x_526);
lean_ctor_set(x_615, 1, x_614);
lean_inc(x_526);
x_616 = l_Lean_Syntax_node1(x_526, x_613, x_615);
lean_inc(x_521);
lean_inc(x_526);
x_617 = l_Lean_Syntax_node1(x_526, x_521, x_616);
lean_inc(x_521);
lean_inc(x_526);
x_618 = l_Lean_Syntax_node1(x_526, x_521, x_617);
x_619 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_523);
x_620 = l_Lean_Name_mkStr4(x_523, x_536, x_537, x_619);
x_621 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_526);
x_622 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_622, 0, x_526);
lean_ctor_set(x_622, 1, x_621);
x_623 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_624 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_625 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_626 = l_Lean_addMacroScope(x_524, x_625, x_527);
x_627 = l_Lean_Name_mkStr3(x_523, x_528, x_623);
x_628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_628, 0, x_627);
lean_ctor_set(x_628, 1, x_554);
x_629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_554);
lean_inc(x_526);
x_630 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_630, 0, x_526);
lean_ctor_set(x_630, 1, x_624);
lean_ctor_set(x_630, 2, x_626);
lean_ctor_set(x_630, 3, x_629);
lean_inc(x_526);
x_631 = l_Lean_Syntax_node2(x_526, x_620, x_622, x_630);
lean_inc_ref(x_585);
lean_inc(x_526);
x_632 = l_Lean_Syntax_node4(x_526, x_608, x_611, x_618, x_585, x_631);
x_633 = lean_array_push(x_609, x_632);
lean_inc(x_521);
lean_inc(x_526);
x_634 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_634, 0, x_526);
lean_ctor_set(x_634, 1, x_521);
lean_ctor_set(x_634, 2, x_633);
lean_inc(x_526);
x_635 = l_Lean_Syntax_node1(x_526, x_606, x_634);
lean_inc_ref_n(x_583, 2);
lean_inc(x_526);
x_636 = l_Lean_Syntax_node6(x_526, x_597, x_598, x_583, x_583, x_602, x_604, x_635);
lean_inc_ref(x_585);
lean_inc_ref(x_583);
lean_inc(x_573);
lean_inc(x_526);
x_637 = l_Lean_Syntax_node4(x_526, x_573, x_595, x_583, x_585, x_636);
lean_inc_ref(x_571);
lean_inc(x_570);
lean_inc(x_526);
x_638 = l_Lean_Syntax_node2(x_526, x_570, x_571, x_637);
lean_inc(x_526);
x_639 = l_Lean_Syntax_node2(x_526, x_521, x_581, x_638);
lean_inc(x_526);
x_640 = l_Lean_Syntax_node2(x_526, x_587, x_594, x_639);
lean_inc(x_526);
x_641 = l_Lean_Syntax_node4(x_526, x_573, x_582, x_583, x_585, x_640);
lean_inc(x_526);
x_642 = l_Lean_Syntax_node2(x_526, x_570, x_571, x_641);
x_643 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__28, &l_Lean_Elab_Command_elabElabRulesAux___closed__28_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__28);
x_644 = lean_array_push(x_643, x_535);
x_645 = lean_array_push(x_644, x_549);
x_646 = lean_array_push(x_645, x_520);
x_647 = lean_array_push(x_646, x_550);
x_648 = lean_array_push(x_647, x_557);
x_649 = lean_array_push(x_648, x_559);
x_650 = lean_array_push(x_649, x_566);
x_651 = lean_array_push(x_650, x_568);
x_652 = lean_array_push(x_651, x_642);
x_653 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_653, 0, x_526);
lean_ctor_set(x_653, 1, x_532);
lean_ctor_set(x_653, 2, x_652);
x_654 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_654, 0, x_653);
return x_654;
}
block_672:
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_663 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_664 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
x_665 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_666 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_667 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_668 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_669; lean_object* x_670; 
x_669 = lean_ctor_get(x_1, 0);
lean_inc(x_669);
lean_dec_ref(x_1);
x_670 = l_Array_mkArray1___redArg(x_669);
x_520 = x_656;
x_521 = x_667;
x_522 = lean_box(0);
x_523 = x_663;
x_524 = x_661;
x_525 = x_658;
x_526 = x_660;
x_527 = x_659;
x_528 = x_664;
x_529 = x_668;
x_530 = x_665;
x_531 = x_657;
x_532 = x_666;
x_533 = x_670;
goto block_655;
}
else
{
lean_object* x_671; 
lean_dec(x_1);
x_671 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_520 = x_656;
x_521 = x_667;
x_522 = lean_box(0);
x_523 = x_663;
x_524 = x_661;
x_525 = x_658;
x_526 = x_660;
x_527 = x_659;
x_528 = x_664;
x_529 = x_668;
x_530 = x_665;
x_531 = x_657;
x_532 = x_666;
x_533 = x_671;
goto block_655;
}
}
block_791:
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
lean_inc_ref(x_673);
x_687 = l_Array_append___redArg(x_673, x_686);
lean_dec_ref(x_686);
lean_inc(x_681);
lean_inc(x_683);
x_688 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_688, 0, x_683);
lean_ctor_set(x_688, 1, x_681);
lean_ctor_set(x_688, 2, x_687);
x_689 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_690 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_691 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_684);
x_692 = l_Lean_Name_mkStr4(x_684, x_689, x_690, x_691);
x_693 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_683);
x_694 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_694, 0, x_683);
lean_ctor_set(x_694, 1, x_693);
x_695 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_696 = l_Lean_Syntax_SepArray_ofElems(x_695, x_674);
lean_dec_ref(x_674);
lean_inc_ref(x_673);
x_697 = l_Array_append___redArg(x_673, x_696);
lean_dec_ref(x_696);
lean_inc(x_681);
lean_inc(x_683);
x_698 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_698, 0, x_683);
lean_ctor_set(x_698, 1, x_681);
lean_ctor_set(x_698, 2, x_697);
x_699 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_683);
x_700 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_700, 0, x_683);
lean_ctor_set(x_700, 1, x_699);
lean_inc(x_683);
x_701 = l_Lean_Syntax_node3(x_683, x_692, x_694, x_698, x_700);
lean_inc(x_681);
lean_inc(x_683);
x_702 = l_Lean_Syntax_node1(x_683, x_681, x_701);
lean_inc(x_683);
x_703 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_703, 0, x_683);
lean_ctor_set(x_703, 1, x_685);
x_704 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_705 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_677);
lean_inc(x_682);
x_706 = l_Lean_addMacroScope(x_682, x_705, x_677);
x_707 = lean_box(0);
lean_inc(x_683);
x_708 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_708, 0, x_683);
lean_ctor_set(x_708, 1, x_704);
lean_ctor_set(x_708, 2, x_706);
lean_ctor_set(x_708, 3, x_707);
x_709 = lean_mk_syntax_ident(x_4);
lean_inc(x_681);
lean_inc(x_683);
x_710 = l_Lean_Syntax_node2(x_683, x_681, x_708, x_709);
x_711 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_683);
x_712 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_712, 0, x_683);
lean_ctor_set(x_712, 1, x_711);
x_713 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__38, &l_Lean_Elab_Command_elabElabRulesAux___closed__38_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__38);
x_714 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
x_715 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
lean_inc_ref(x_676);
lean_inc_ref(x_684);
x_716 = l_Lean_Name_mkStr4(x_684, x_676, x_714, x_715);
lean_inc(x_677);
lean_inc(x_716);
lean_inc(x_682);
x_717 = l_Lean_addMacroScope(x_682, x_716, x_677);
x_718 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_718, 0, x_716);
lean_ctor_set(x_718, 1, x_707);
x_719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_719, 0, x_718);
lean_ctor_set(x_719, 1, x_707);
lean_inc(x_683);
x_720 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_720, 0, x_683);
lean_ctor_set(x_720, 1, x_713);
lean_ctor_set(x_720, 2, x_717);
lean_ctor_set(x_720, 3, x_719);
x_721 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_683);
x_722 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_722, 0, x_683);
lean_ctor_set(x_722, 1, x_721);
x_723 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_684);
x_724 = l_Lean_Name_mkStr4(x_684, x_689, x_690, x_723);
lean_inc(x_683);
x_725 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_725, 0, x_683);
lean_ctor_set(x_725, 1, x_723);
x_726 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(x_684);
x_727 = l_Lean_Name_mkStr4(x_684, x_689, x_690, x_726);
x_728 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
x_729 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(x_677);
lean_inc(x_682);
x_730 = l_Lean_addMacroScope(x_682, x_729, x_677);
lean_inc(x_683);
x_731 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_731, 0, x_683);
lean_ctor_set(x_731, 1, x_728);
lean_ctor_set(x_731, 2, x_730);
lean_ctor_set(x_731, 3, x_707);
lean_inc_ref(x_731);
lean_inc(x_681);
lean_inc(x_683);
x_732 = l_Lean_Syntax_node2(x_683, x_681, x_731, x_680);
lean_inc_ref(x_673);
lean_inc(x_681);
lean_inc(x_683);
x_733 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_733, 0, x_683);
lean_ctor_set(x_733, 1, x_681);
lean_ctor_set(x_733, 2, x_673);
x_734 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_683);
x_735 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_735, 0, x_683);
lean_ctor_set(x_735, 1, x_734);
x_736 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(x_684);
x_737 = l_Lean_Name_mkStr4(x_684, x_689, x_690, x_736);
lean_inc(x_683);
x_738 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_738, 0, x_683);
lean_ctor_set(x_738, 1, x_736);
x_739 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(x_684);
x_740 = l_Lean_Name_mkStr4(x_684, x_689, x_690, x_739);
lean_inc_ref(x_733);
lean_inc(x_683);
x_741 = l_Lean_Syntax_node2(x_683, x_740, x_733, x_731);
lean_inc(x_681);
lean_inc(x_683);
x_742 = l_Lean_Syntax_node1(x_683, x_681, x_741);
x_743 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(x_683);
x_744 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_744, 0, x_683);
lean_ctor_set(x_744, 1, x_743);
x_745 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_684);
x_746 = l_Lean_Name_mkStr4(x_684, x_689, x_690, x_745);
x_747 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_684);
x_748 = l_Lean_Name_mkStr4(x_684, x_689, x_690, x_747);
x_749 = l_Array_append___redArg(x_673, x_14);
lean_dec(x_14);
x_750 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_683);
x_751 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_751, 0, x_683);
lean_ctor_set(x_751, 1, x_750);
x_752 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_684);
x_753 = l_Lean_Name_mkStr4(x_684, x_689, x_690, x_752);
x_754 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_683);
x_755 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_755, 0, x_683);
lean_ctor_set(x_755, 1, x_754);
lean_inc(x_683);
x_756 = l_Lean_Syntax_node1(x_683, x_753, x_755);
lean_inc(x_681);
lean_inc(x_683);
x_757 = l_Lean_Syntax_node1(x_683, x_681, x_756);
lean_inc(x_681);
lean_inc(x_683);
x_758 = l_Lean_Syntax_node1(x_683, x_681, x_757);
x_759 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_684);
x_760 = l_Lean_Name_mkStr4(x_684, x_689, x_690, x_759);
x_761 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_683);
x_762 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_762, 0, x_683);
lean_ctor_set(x_762, 1, x_761);
x_763 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_764 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_765 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_766 = l_Lean_addMacroScope(x_682, x_765, x_677);
x_767 = l_Lean_Name_mkStr3(x_684, x_676, x_763);
x_768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_768, 0, x_767);
lean_ctor_set(x_768, 1, x_707);
x_769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_707);
lean_inc(x_683);
x_770 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_770, 0, x_683);
lean_ctor_set(x_770, 1, x_764);
lean_ctor_set(x_770, 2, x_766);
lean_ctor_set(x_770, 3, x_769);
lean_inc(x_683);
x_771 = l_Lean_Syntax_node2(x_683, x_760, x_762, x_770);
lean_inc_ref(x_735);
lean_inc(x_683);
x_772 = l_Lean_Syntax_node4(x_683, x_748, x_751, x_758, x_735, x_771);
x_773 = lean_array_push(x_749, x_772);
lean_inc(x_683);
x_774 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_774, 0, x_683);
lean_ctor_set(x_774, 1, x_681);
lean_ctor_set(x_774, 2, x_773);
lean_inc(x_683);
x_775 = l_Lean_Syntax_node1(x_683, x_746, x_774);
lean_inc_ref_n(x_733, 2);
lean_inc(x_683);
x_776 = l_Lean_Syntax_node6(x_683, x_737, x_738, x_733, x_733, x_742, x_744, x_775);
lean_inc(x_683);
x_777 = l_Lean_Syntax_node4(x_683, x_727, x_732, x_733, x_735, x_776);
lean_inc(x_683);
x_778 = l_Lean_Syntax_node2(x_683, x_724, x_725, x_777);
x_779 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__28, &l_Lean_Elab_Command_elabElabRulesAux___closed__28_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__28);
x_780 = lean_array_push(x_779, x_688);
x_781 = lean_array_push(x_780, x_702);
x_782 = lean_array_push(x_781, x_675);
x_783 = lean_array_push(x_782, x_703);
x_784 = lean_array_push(x_783, x_710);
x_785 = lean_array_push(x_784, x_712);
x_786 = lean_array_push(x_785, x_720);
x_787 = lean_array_push(x_786, x_722);
x_788 = lean_array_push(x_787, x_778);
x_789 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_789, 0, x_683);
lean_ctor_set(x_789, 1, x_678);
lean_ctor_set(x_789, 2, x_788);
x_790 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_790, 0, x_789);
return x_790;
}
block_808:
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_799 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_800 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
x_801 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_802 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_803 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_804 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_805; lean_object* x_806; 
x_805 = lean_ctor_get(x_1, 0);
lean_inc(x_805);
lean_dec_ref(x_1);
x_806 = l_Array_mkArray1___redArg(x_805);
x_673 = x_804;
x_674 = x_792;
x_675 = x_793;
x_676 = x_800;
x_677 = x_794;
x_678 = x_802;
x_679 = lean_box(0);
x_680 = x_796;
x_681 = x_803;
x_682 = x_797;
x_683 = x_795;
x_684 = x_799;
x_685 = x_801;
x_686 = x_806;
goto block_791;
}
else
{
lean_object* x_807; 
lean_dec(x_1);
x_807 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_673 = x_804;
x_674 = x_792;
x_675 = x_793;
x_676 = x_800;
x_677 = x_794;
x_678 = x_802;
x_679 = lean_box(0);
x_680 = x_796;
x_681 = x_803;
x_682 = x_797;
x_683 = x_795;
x_684 = x_799;
x_685 = x_801;
x_686 = x_807;
goto block_791;
}
}
block_842:
{
lean_object* x_815; 
lean_inc(x_4);
x_815 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_811, x_810, x_813);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
lean_dec_ref(x_815);
x_817 = l_Lean_Elab_Command_getRef___redArg(x_810);
if (lean_obj_tag(x_817) == 0)
{
lean_object* x_818; lean_object* x_819; 
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
lean_dec_ref(x_817);
x_819 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_810);
if (lean_obj_tag(x_819) == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
lean_dec_ref(x_819);
x_821 = lean_ctor_get(x_810, 5);
lean_inc(x_821);
lean_dec_ref(x_810);
x_822 = l_Lean_SourceInfo_fromRef(x_818, x_812);
lean_dec(x_818);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_823; lean_object* x_824; 
x_823 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_813);
x_824 = lean_ctor_get(x_823, 0);
lean_inc(x_824);
lean_dec_ref(x_823);
x_504 = x_809;
x_505 = x_822;
x_506 = x_816;
x_507 = x_820;
x_508 = x_824;
x_509 = lean_box(0);
goto block_519;
}
else
{
lean_object* x_825; 
x_825 = lean_ctor_get(x_821, 0);
lean_inc(x_825);
lean_dec_ref(x_821);
x_504 = x_809;
x_505 = x_822;
x_506 = x_816;
x_507 = x_820;
x_508 = x_825;
x_509 = lean_box(0);
goto block_519;
}
}
else
{
lean_object* x_826; lean_object* x_827; uint8_t x_828; uint8_t x_833; 
lean_dec(x_818);
lean_dec(x_816);
lean_dec_ref(x_810);
lean_dec(x_809);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_826 = lean_ctor_get(x_819, 0);
x_833 = !lean_is_exclusive(x_819);
if (x_833 == 0)
{
x_827 = x_819;
x_828 = x_833;
goto block_832;
}
else
{
lean_inc(x_826);
lean_dec(x_819);
x_827 = lean_box(0);
x_828 = x_833;
goto block_832;
}
block_832:
{
lean_object* x_829; 
if (x_828 == 0)
{
x_829 = x_827;
goto block_830;
}
else
{
lean_object* x_831; 
x_831 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_831, 0, x_826);
x_829 = x_831;
goto block_830;
}
block_830:
{
return x_829;
}
}
}
}
else
{
lean_dec(x_816);
lean_dec_ref(x_810);
lean_dec(x_809);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_817;
}
}
else
{
lean_object* x_834; lean_object* x_835; uint8_t x_836; uint8_t x_841; 
lean_dec_ref(x_810);
lean_dec(x_809);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_834 = lean_ctor_get(x_815, 0);
x_841 = !lean_is_exclusive(x_815);
if (x_841 == 0)
{
x_835 = x_815;
x_836 = x_841;
goto block_840;
}
else
{
lean_inc(x_834);
lean_dec(x_815);
x_835 = lean_box(0);
x_836 = x_841;
goto block_840;
}
block_840:
{
lean_object* x_837; 
if (x_836 == 0)
{
x_837 = x_835;
goto block_838;
}
else
{
lean_object* x_839; 
x_839 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_839, 0, x_834);
x_837 = x_839;
goto block_838;
}
block_838:
{
return x_837;
}
}
}
}
block_1017:
{
lean_object* x_847; 
lean_inc(x_3);
x_847 = l_Lean_Parser_Command_visibility_ofAttrKind(x_3);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_848; lean_object* x_849; uint8_t x_850; 
lean_del_object(x_15);
x_848 = lean_ctor_get(x_6, 0);
lean_inc(x_848);
lean_dec_ref(x_6);
x_849 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__55));
x_850 = lean_name_eq(x_843, x_849);
if (x_850 == 0)
{
lean_object* x_851; uint8_t x_852; 
x_851 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__57));
x_852 = lean_name_eq(x_843, x_851);
if (x_852 == 0)
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
lean_dec(x_847);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_853 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__59, &l_Lean_Elab_Command_elabElabRulesAux___closed__59_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__59);
x_854 = l_Lean_MessageData_ofName(x_843);
x_855 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_855, 0, x_853);
lean_ctor_set(x_855, 1, x_854);
x_856 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__61, &l_Lean_Elab_Command_elabElabRulesAux___closed__61_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__61);
x_857 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_857, 1, x_856);
x_858 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_848, x_857, x_844, x_845);
lean_dec(x_848);
return x_858;
}
else
{
lean_object* x_859; lean_object* x_860; 
lean_dec(x_843);
x_859 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__63));
lean_inc(x_4);
x_860 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_859, x_844, x_845);
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; 
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
lean_dec_ref(x_860);
x_862 = l_Lean_Elab_Command_getRef___redArg(x_844);
if (lean_obj_tag(x_862) == 0)
{
lean_object* x_863; lean_object* x_864; 
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
lean_dec_ref(x_862);
x_864 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_844);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
lean_dec_ref(x_864);
x_866 = lean_ctor_get(x_844, 5);
lean_inc(x_866);
lean_dec_ref(x_844);
x_867 = l_Lean_SourceInfo_fromRef(x_863, x_850);
lean_dec(x_863);
if (lean_obj_tag(x_866) == 0)
{
lean_object* x_868; lean_object* x_869; 
x_868 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_845);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
lean_dec_ref(x_868);
x_792 = x_861;
x_793 = x_847;
x_794 = x_865;
x_795 = x_867;
x_796 = x_848;
x_797 = x_869;
x_798 = lean_box(0);
goto block_808;
}
else
{
lean_object* x_870; 
x_870 = lean_ctor_get(x_866, 0);
lean_inc(x_870);
lean_dec_ref(x_866);
x_792 = x_861;
x_793 = x_847;
x_794 = x_865;
x_795 = x_867;
x_796 = x_848;
x_797 = x_870;
x_798 = lean_box(0);
goto block_808;
}
}
else
{
lean_object* x_871; lean_object* x_872; uint8_t x_873; uint8_t x_878; 
lean_dec(x_863);
lean_dec(x_861);
lean_dec(x_848);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_871 = lean_ctor_get(x_864, 0);
x_878 = !lean_is_exclusive(x_864);
if (x_878 == 0)
{
x_872 = x_864;
x_873 = x_878;
goto block_877;
}
else
{
lean_inc(x_871);
lean_dec(x_864);
x_872 = lean_box(0);
x_873 = x_878;
goto block_877;
}
block_877:
{
lean_object* x_874; 
if (x_873 == 0)
{
x_874 = x_872;
goto block_875;
}
else
{
lean_object* x_876; 
x_876 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_876, 0, x_871);
x_874 = x_876;
goto block_875;
}
block_875:
{
return x_874;
}
}
}
}
else
{
lean_dec(x_861);
lean_dec(x_848);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_862;
}
}
else
{
lean_object* x_879; lean_object* x_880; uint8_t x_881; uint8_t x_886; 
lean_dec(x_848);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_879 = lean_ctor_get(x_860, 0);
x_886 = !lean_is_exclusive(x_860);
if (x_886 == 0)
{
x_880 = x_860;
x_881 = x_886;
goto block_885;
}
else
{
lean_inc(x_879);
lean_dec(x_860);
x_880 = lean_box(0);
x_881 = x_886;
goto block_885;
}
block_885:
{
lean_object* x_882; 
if (x_881 == 0)
{
x_882 = x_880;
goto block_883;
}
else
{
lean_object* x_884; 
x_884 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_884, 0, x_879);
x_882 = x_884;
goto block_883;
}
block_883:
{
return x_882;
}
}
}
}
}
else
{
lean_object* x_887; lean_object* x_888; 
lean_dec(x_843);
x_887 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__65));
lean_inc(x_4);
x_888 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_887, x_844, x_845);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; lean_object* x_890; 
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
lean_dec_ref(x_888);
x_890 = l_Lean_Elab_Command_getRef___redArg(x_844);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
lean_dec_ref(x_890);
x_892 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_844);
if (lean_obj_tag(x_892) == 0)
{
lean_object* x_893; lean_object* x_894; uint8_t x_895; lean_object* x_896; 
x_893 = lean_ctor_get(x_892, 0);
lean_inc(x_893);
lean_dec_ref(x_892);
x_894 = lean_ctor_get(x_844, 5);
lean_inc(x_894);
lean_dec_ref(x_844);
x_895 = 0;
x_896 = l_Lean_SourceInfo_fromRef(x_891, x_895);
lean_dec(x_891);
if (lean_obj_tag(x_894) == 0)
{
lean_object* x_897; lean_object* x_898; 
x_897 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_845);
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
lean_dec_ref(x_897);
x_656 = x_847;
x_657 = x_889;
x_658 = x_848;
x_659 = x_893;
x_660 = x_896;
x_661 = x_898;
x_662 = lean_box(0);
goto block_672;
}
else
{
lean_object* x_899; 
x_899 = lean_ctor_get(x_894, 0);
lean_inc(x_899);
lean_dec_ref(x_894);
x_656 = x_847;
x_657 = x_889;
x_658 = x_848;
x_659 = x_893;
x_660 = x_896;
x_661 = x_899;
x_662 = lean_box(0);
goto block_672;
}
}
else
{
lean_object* x_900; lean_object* x_901; uint8_t x_902; uint8_t x_907; 
lean_dec(x_891);
lean_dec(x_889);
lean_dec(x_848);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_900 = lean_ctor_get(x_892, 0);
x_907 = !lean_is_exclusive(x_892);
if (x_907 == 0)
{
x_901 = x_892;
x_902 = x_907;
goto block_906;
}
else
{
lean_inc(x_900);
lean_dec(x_892);
x_901 = lean_box(0);
x_902 = x_907;
goto block_906;
}
block_906:
{
lean_object* x_903; 
if (x_902 == 0)
{
x_903 = x_901;
goto block_904;
}
else
{
lean_object* x_905; 
x_905 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_905, 0, x_900);
x_903 = x_905;
goto block_904;
}
block_904:
{
return x_903;
}
}
}
}
else
{
lean_dec(x_889);
lean_dec(x_848);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_890;
}
}
else
{
lean_object* x_908; lean_object* x_909; uint8_t x_910; uint8_t x_915; 
lean_dec(x_848);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_908 = lean_ctor_get(x_888, 0);
x_915 = !lean_is_exclusive(x_888);
if (x_915 == 0)
{
x_909 = x_888;
x_910 = x_915;
goto block_914;
}
else
{
lean_inc(x_908);
lean_dec(x_888);
x_909 = lean_box(0);
x_910 = x_915;
goto block_914;
}
block_914:
{
lean_object* x_911; 
if (x_910 == 0)
{
x_911 = x_909;
goto block_912;
}
else
{
lean_object* x_913; 
x_913 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_913, 0, x_908);
x_911 = x_913;
goto block_912;
}
block_912:
{
return x_911;
}
}
}
}
}
else
{
lean_object* x_916; uint8_t x_917; 
lean_dec(x_6);
x_916 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__55));
x_917 = lean_name_eq(x_843, x_916);
if (x_917 == 0)
{
lean_object* x_918; uint8_t x_919; 
lean_del_object(x_15);
x_918 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__67));
x_919 = lean_name_eq(x_843, x_918);
if (x_919 == 0)
{
lean_object* x_920; uint8_t x_921; 
x_920 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__69));
x_921 = lean_name_eq(x_843, x_920);
if (x_921 == 0)
{
lean_object* x_922; uint8_t x_923; 
x_922 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__71));
x_923 = lean_name_eq(x_843, x_922);
if (x_923 == 0)
{
lean_object* x_924; uint8_t x_925; 
x_924 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__57));
x_925 = lean_name_eq(x_843, x_924);
if (x_925 == 0)
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; 
lean_dec(x_847);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_926 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__73, &l_Lean_Elab_Command_elabElabRulesAux___closed__73_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__73);
x_927 = l_Lean_MessageData_ofName(x_843);
x_928 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_928, 0, x_926);
lean_ctor_set(x_928, 1, x_927);
x_929 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
x_930 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_930, 0, x_928);
lean_ctor_set(x_930, 1, x_929);
x_931 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(x_930, x_844, x_845);
return x_931;
}
else
{
lean_object* x_932; lean_object* x_933; 
lean_dec(x_843);
x_932 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__63));
lean_inc(x_4);
x_933 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_932, x_844, x_845);
if (lean_obj_tag(x_933) == 0)
{
lean_object* x_934; lean_object* x_935; 
x_934 = lean_ctor_get(x_933, 0);
lean_inc(x_934);
lean_dec_ref(x_933);
x_935 = l_Lean_Elab_Command_getRef___redArg(x_844);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; 
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
lean_dec_ref(x_935);
x_937 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_844);
if (lean_obj_tag(x_937) == 0)
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_938 = lean_ctor_get(x_937, 0);
lean_inc(x_938);
lean_dec_ref(x_937);
x_939 = lean_ctor_get(x_844, 5);
lean_inc(x_939);
lean_dec_ref(x_844);
x_940 = l_Lean_SourceInfo_fromRef(x_936, x_923);
lean_dec(x_936);
if (lean_obj_tag(x_939) == 0)
{
lean_object* x_941; lean_object* x_942; 
x_941 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_845);
x_942 = lean_ctor_get(x_941, 0);
lean_inc(x_942);
lean_dec_ref(x_941);
x_390 = x_938;
x_391 = x_847;
x_392 = x_940;
x_393 = x_934;
x_394 = x_942;
x_395 = lean_box(0);
goto block_405;
}
else
{
lean_object* x_943; 
x_943 = lean_ctor_get(x_939, 0);
lean_inc(x_943);
lean_dec_ref(x_939);
x_390 = x_938;
x_391 = x_847;
x_392 = x_940;
x_393 = x_934;
x_394 = x_943;
x_395 = lean_box(0);
goto block_405;
}
}
else
{
lean_object* x_944; lean_object* x_945; uint8_t x_946; uint8_t x_951; 
lean_dec(x_936);
lean_dec(x_934);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_944 = lean_ctor_get(x_937, 0);
x_951 = !lean_is_exclusive(x_937);
if (x_951 == 0)
{
x_945 = x_937;
x_946 = x_951;
goto block_950;
}
else
{
lean_inc(x_944);
lean_dec(x_937);
x_945 = lean_box(0);
x_946 = x_951;
goto block_950;
}
block_950:
{
lean_object* x_947; 
if (x_946 == 0)
{
x_947 = x_945;
goto block_948;
}
else
{
lean_object* x_949; 
x_949 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_949, 0, x_944);
x_947 = x_949;
goto block_948;
}
block_948:
{
return x_947;
}
}
}
}
else
{
lean_dec(x_934);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_935;
}
}
else
{
lean_object* x_952; lean_object* x_953; uint8_t x_954; uint8_t x_959; 
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_952 = lean_ctor_get(x_933, 0);
x_959 = !lean_is_exclusive(x_933);
if (x_959 == 0)
{
x_953 = x_933;
x_954 = x_959;
goto block_958;
}
else
{
lean_inc(x_952);
lean_dec(x_933);
x_953 = lean_box(0);
x_954 = x_959;
goto block_958;
}
block_958:
{
lean_object* x_955; 
if (x_954 == 0)
{
x_955 = x_953;
goto block_956;
}
else
{
lean_object* x_957; 
x_957 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_957, 0, x_952);
x_955 = x_957;
goto block_956;
}
block_956:
{
return x_955;
}
}
}
}
}
else
{
lean_dec(x_843);
x_809 = x_847;
x_810 = x_844;
x_811 = x_920;
x_812 = x_919;
x_813 = x_845;
x_814 = lean_box(0);
goto block_842;
}
}
else
{
lean_dec(x_843);
x_809 = x_847;
x_810 = x_844;
x_811 = x_920;
x_812 = x_919;
x_813 = x_845;
x_814 = lean_box(0);
goto block_842;
}
}
else
{
lean_object* x_960; lean_object* x_961; 
lean_dec(x_843);
x_960 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__75));
lean_inc(x_4);
x_961 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_960, x_844, x_845);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; lean_object* x_963; 
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
lean_dec_ref(x_961);
x_963 = l_Lean_Elab_Command_getRef___redArg(x_844);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; lean_object* x_965; 
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
lean_dec_ref(x_963);
x_965 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_844);
if (lean_obj_tag(x_965) == 0)
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
lean_dec_ref(x_965);
x_967 = lean_ctor_get(x_844, 5);
lean_inc(x_967);
lean_dec_ref(x_844);
x_968 = l_Lean_SourceInfo_fromRef(x_964, x_917);
lean_dec(x_964);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_969; lean_object* x_970; 
x_969 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_845);
x_970 = lean_ctor_get(x_969, 0);
lean_inc(x_970);
lean_dec_ref(x_969);
x_251 = x_968;
x_252 = x_847;
x_253 = x_962;
x_254 = x_966;
x_255 = x_970;
x_256 = lean_box(0);
goto block_267;
}
else
{
lean_object* x_971; 
x_971 = lean_ctor_get(x_967, 0);
lean_inc(x_971);
lean_dec_ref(x_967);
x_251 = x_968;
x_252 = x_847;
x_253 = x_962;
x_254 = x_966;
x_255 = x_971;
x_256 = lean_box(0);
goto block_267;
}
}
else
{
lean_object* x_972; lean_object* x_973; uint8_t x_974; uint8_t x_979; 
lean_dec(x_964);
lean_dec(x_962);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_972 = lean_ctor_get(x_965, 0);
x_979 = !lean_is_exclusive(x_965);
if (x_979 == 0)
{
x_973 = x_965;
x_974 = x_979;
goto block_978;
}
else
{
lean_inc(x_972);
lean_dec(x_965);
x_973 = lean_box(0);
x_974 = x_979;
goto block_978;
}
block_978:
{
lean_object* x_975; 
if (x_974 == 0)
{
x_975 = x_973;
goto block_976;
}
else
{
lean_object* x_977; 
x_977 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_977, 0, x_972);
x_975 = x_977;
goto block_976;
}
block_976:
{
return x_975;
}
}
}
}
else
{
lean_dec(x_962);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_963;
}
}
else
{
lean_object* x_980; lean_object* x_981; uint8_t x_982; uint8_t x_987; 
lean_dec(x_847);
lean_dec_ref(x_844);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_980 = lean_ctor_get(x_961, 0);
x_987 = !lean_is_exclusive(x_961);
if (x_987 == 0)
{
x_981 = x_961;
x_982 = x_987;
goto block_986;
}
else
{
lean_inc(x_980);
lean_dec(x_961);
x_981 = lean_box(0);
x_982 = x_987;
goto block_986;
}
block_986:
{
lean_object* x_983; 
if (x_982 == 0)
{
x_983 = x_981;
goto block_984;
}
else
{
lean_object* x_985; 
x_985 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_985, 0, x_980);
x_983 = x_985;
goto block_984;
}
block_984:
{
return x_983;
}
}
}
}
}
else
{
lean_object* x_988; lean_object* x_989; 
lean_dec(x_843);
x_988 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__65));
lean_inc(x_4);
x_989 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_988, x_844, x_845);
if (lean_obj_tag(x_989) == 0)
{
lean_object* x_990; lean_object* x_991; 
x_990 = lean_ctor_get(x_989, 0);
lean_inc(x_990);
lean_dec_ref(x_989);
x_991 = l_Lean_Elab_Command_getRef___redArg(x_844);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; lean_object* x_993; 
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
lean_dec_ref(x_991);
x_993 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_844);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; uint8_t x_996; lean_object* x_997; 
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
lean_dec_ref(x_993);
x_995 = lean_ctor_get(x_844, 5);
lean_inc(x_995);
lean_dec_ref(x_844);
x_996 = 0;
x_997 = l_Lean_SourceInfo_fromRef(x_992, x_996);
lean_dec(x_992);
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_998; lean_object* x_999; 
x_998 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_845);
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
lean_dec_ref(x_998);
x_136 = x_994;
x_137 = x_997;
x_138 = x_847;
x_139 = x_990;
x_140 = x_999;
x_141 = lean_box(0);
goto block_151;
}
else
{
lean_object* x_1000; 
x_1000 = lean_ctor_get(x_995, 0);
lean_inc(x_1000);
lean_dec_ref(x_995);
x_136 = x_994;
x_137 = x_997;
x_138 = x_847;
x_139 = x_990;
x_140 = x_1000;
x_141 = lean_box(0);
goto block_151;
}
}
else
{
lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; uint8_t x_1008; 
lean_dec(x_992);
lean_dec(x_990);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_1001 = lean_ctor_get(x_993, 0);
x_1008 = !lean_is_exclusive(x_993);
if (x_1008 == 0)
{
x_1002 = x_993;
x_1003 = x_1008;
goto block_1007;
}
else
{
lean_inc(x_1001);
lean_dec(x_993);
x_1002 = lean_box(0);
x_1003 = x_1008;
goto block_1007;
}
block_1007:
{
lean_object* x_1004; 
if (x_1003 == 0)
{
x_1004 = x_1002;
goto block_1005;
}
else
{
lean_object* x_1006; 
x_1006 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1006, 0, x_1001);
x_1004 = x_1006;
goto block_1005;
}
block_1005:
{
return x_1004;
}
}
}
}
else
{
lean_dec(x_990);
lean_dec(x_847);
lean_dec_ref(x_844);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_991;
}
}
else
{
lean_object* x_1009; lean_object* x_1010; uint8_t x_1011; uint8_t x_1016; 
lean_dec(x_847);
lean_dec_ref(x_844);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_1009 = lean_ctor_get(x_989, 0);
x_1016 = !lean_is_exclusive(x_989);
if (x_1016 == 0)
{
x_1010 = x_989;
x_1011 = x_1016;
goto block_1015;
}
else
{
lean_inc(x_1009);
lean_dec(x_989);
x_1010 = lean_box(0);
x_1011 = x_1016;
goto block_1015;
}
block_1015:
{
lean_object* x_1012; 
if (x_1011 == 0)
{
x_1012 = x_1010;
goto block_1013;
}
else
{
lean_object* x_1014; 
x_1014 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1014, 0, x_1009);
x_1012 = x_1014;
goto block_1013;
}
block_1013:
{
return x_1012;
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
lean_object* x_1033; lean_object* x_1034; uint8_t x_1035; uint8_t x_1040; 
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1033 = lean_ctor_get(x_13, 0);
x_1040 = !lean_is_exclusive(x_13);
if (x_1040 == 0)
{
x_1034 = x_13;
x_1035 = x_1040;
goto block_1039;
}
else
{
lean_inc(x_1033);
lean_dec(x_13);
x_1034 = lean_box(0);
x_1035 = x_1040;
goto block_1039;
}
block_1039:
{
lean_object* x_1036; 
if (x_1035 == 0)
{
x_1036 = x_1034;
goto block_1037;
}
else
{
lean_object* x_1038; 
x_1038 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1038, 0, x_1033);
x_1036 = x_1038;
goto block_1037;
}
block_1037:
{
return x_1036;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabElabRulesAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabElabRules___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Elab_Command_getRef___redArg(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; uint8_t x_126; 
x_126 = !lean_is_exclusive(x_21);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_21, 0);
lean_dec(x_127);
x_22 = x_21;
x_23 = x_126;
goto block_125;
}
else
{
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_117; 
x_24 = lean_ctor_get(x_16, 5);
x_25 = 0;
x_26 = l_Lean_SourceInfo_fromRef(x_20, x_25);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_124; 
x_124 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_17);
lean_dec_ref(x_124);
x_117 = lean_box(0);
goto block_123;
}
else
{
x_117 = lean_box(0);
goto block_123;
}
block_45:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_inc_ref(x_29);
x_36 = l_Array_append___redArg(x_29, x_35);
lean_dec_ref(x_35);
lean_inc(x_28);
lean_inc(x_26);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_Array_append___redArg(x_29, x_15);
lean_inc(x_26);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_38);
lean_inc(x_26);
x_40 = l_Lean_Syntax_node1(x_26, x_1, x_39);
x_41 = l_Lean_Syntax_node8(x_26, x_2, x_31, x_34, x_3, x_27, x_33, x_32, x_37, x_40);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_41);
x_42 = x_22;
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
block_61:
{
lean_object* x_54; lean_object* x_55; 
lean_inc_ref(x_48);
x_54 = l_Array_append___redArg(x_48, x_53);
lean_dec_ref(x_53);
lean_inc(x_47);
lean_inc(x_26);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_26);
lean_ctor_set(x_55, 1, x_47);
lean_ctor_set(x_55, 2, x_54);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_5);
x_56 = lean_ctor_get(x_4, 0);
lean_inc(x_56);
lean_dec_ref(x_4);
x_57 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(x_26);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_26);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_mkArray2___redArg(x_58, x_56);
x_27 = x_46;
x_28 = x_47;
x_29 = x_48;
x_30 = lean_box(0);
x_31 = x_50;
x_32 = x_55;
x_33 = x_51;
x_34 = x_52;
x_35 = x_59;
goto block_45;
}
else
{
lean_object* x_60; 
x_60 = lean_apply_1(x_5, x_4);
x_27 = x_46;
x_28 = x_47;
x_29 = x_48;
x_30 = lean_box(0);
x_31 = x_50;
x_32 = x_55;
x_33 = x_51;
x_34 = x_52;
x_35 = x_60;
goto block_45;
}
}
block_76:
{
lean_object* x_69; lean_object* x_70; 
lean_inc_ref(x_64);
x_69 = l_Array_append___redArg(x_64, x_68);
lean_dec_ref(x_68);
lean_inc(x_63);
lean_inc(x_26);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_26);
lean_ctor_set(x_70, 1, x_63);
lean_ctor_set(x_70, 2, x_69);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_6, 0);
lean_inc(x_71);
lean_dec_ref(x_6);
x_72 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_26);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_26);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Array_mkArray2___redArg(x_73, x_71);
x_46 = x_62;
x_47 = x_63;
x_48 = x_64;
x_49 = lean_box(0);
x_50 = x_66;
x_51 = x_70;
x_52 = x_67;
x_53 = x_74;
goto block_61;
}
else
{
lean_object* x_75; 
lean_inc_ref(x_5);
x_75 = lean_apply_1(x_5, x_6);
x_46 = x_62;
x_47 = x_63;
x_48 = x_64;
x_49 = lean_box(0);
x_50 = x_66;
x_51 = x_70;
x_52 = x_67;
x_53 = x_75;
goto block_61;
}
}
block_97:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_inc_ref(x_78);
x_82 = l_Array_append___redArg(x_78, x_81);
lean_dec_ref(x_81);
lean_inc(x_77);
lean_inc(x_26);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_26);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_82);
lean_inc(x_26);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_26);
lean_ctor_set(x_84, 1, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_85; 
x_85 = lean_mk_empty_array_with_capacity(x_8);
x_62 = x_84;
x_63 = x_77;
x_64 = x_78;
x_65 = lean_box(0);
x_66 = x_80;
x_67 = x_83;
x_68 = x_85;
goto block_76;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_86 = lean_ctor_get(x_14, 0);
lean_inc(x_86);
lean_dec_ref(x_14);
x_87 = lean_mk_syntax_ident(x_86);
x_88 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc(x_26);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_26);
lean_ctor_set(x_89, 1, x_88);
x_90 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
lean_inc(x_26);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_26);
lean_ctor_set(x_91, 1, x_90);
x_92 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_26);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_26);
lean_ctor_set(x_93, 1, x_92);
x_94 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
lean_inc(x_26);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_26);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Array_mkArray5___redArg(x_89, x_91, x_93, x_87, x_95);
x_62 = x_84;
x_63 = x_77;
x_64 = x_78;
x_65 = lean_box(0);
x_66 = x_80;
x_67 = x_83;
x_68 = x_96;
goto block_76;
}
}
block_116:
{
lean_object* x_102; lean_object* x_103; 
lean_inc_ref(x_99);
x_102 = l_Array_append___redArg(x_99, x_101);
lean_dec_ref(x_101);
lean_inc(x_98);
lean_inc(x_26);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_26);
lean_ctor_set(x_103, 1, x_98);
lean_ctor_set(x_103, 2, x_102);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_104 = lean_ctor_get(x_9, 0);
x_105 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
x_106 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_105);
x_107 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_26);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_26);
lean_ctor_set(x_108, 1, x_107);
lean_inc_ref(x_99);
x_109 = l_Array_append___redArg(x_99, x_104);
lean_inc(x_98);
lean_inc(x_26);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_26);
lean_ctor_set(x_110, 1, x_98);
lean_ctor_set(x_110, 2, x_109);
x_111 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_26);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_26);
lean_ctor_set(x_112, 1, x_111);
lean_inc(x_26);
x_113 = l_Lean_Syntax_node3(x_26, x_106, x_108, x_110, x_112);
x_114 = l_Array_mkArray1___redArg(x_113);
x_77 = x_98;
x_78 = x_99;
x_79 = lean_box(0);
x_80 = x_103;
x_81 = x_114;
goto block_97;
}
else
{
lean_object* x_115; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_115 = lean_mk_empty_array_with_capacity(x_8);
x_77 = x_98;
x_78 = x_99;
x_79 = lean_box(0);
x_80 = x_103;
x_81 = x_115;
goto block_97;
}
}
block_123:
{
lean_object* x_118; lean_object* x_119; 
x_118 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_119 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_13, 0);
lean_inc(x_120);
lean_dec_ref(x_13);
x_121 = l_Array_mkArray1___redArg(x_120);
x_98 = x_118;
x_99 = x_119;
x_100 = lean_box(0);
x_101 = x_121;
goto block_116;
}
else
{
lean_object* x_122; 
lean_dec(x_13);
x_122 = lean_mk_empty_array_with_capacity(x_8);
x_98 = x_118;
x_99 = x_119;
x_100 = lean_box(0);
x_101 = x_122;
goto block_116;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_135; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_ctor_get(x_21, 0);
x_135 = !lean_is_exclusive(x_21);
if (x_135 == 0)
{
x_129 = x_21;
x_130 = x_135;
goto block_134;
}
else
{
lean_inc(x_128);
lean_dec(x_21);
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
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_143; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_ctor_get(x_19, 0);
x_143 = !lean_is_exclusive(x_19);
if (x_143 == 0)
{
x_137 = x_19;
x_138 = x_143;
goto block_142;
}
else
{
lean_inc(x_136);
lean_dec(x_19);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Elab_Command_elabElabRules___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec(x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_7 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_8 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
x_9 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(x_2);
x_10 = l_Lean_Syntax_isOfKind(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_171; uint8_t x_172; 
x_12 = lean_unsigned_to_nat(0u);
x_171 = l_Lean_Syntax_getArg(x_2, x_12);
x_172 = l_Lean_Syntax_isNone(x_171);
if (x_172 == 0)
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_unsigned_to_nat(1u);
lean_inc(x_171);
x_174 = l_Lean_Syntax_matchesNull(x_171, x_173);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_171);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_175 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = l_Lean_Syntax_getArg(x_171, x_12);
lean_dec(x_171);
x_177 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(x_176);
x_178 = l_Lean_Syntax_isOfKind(x_176, x_177);
if (x_178 == 0)
{
lean_object* x_179; 
lean_dec(x_176);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_179 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_176);
x_153 = x_180;
x_154 = x_3;
x_155 = x_4;
x_156 = lean_box(0);
goto block_170;
}
}
}
else
{
lean_object* x_181; 
lean_dec(x_171);
x_181 = lean_box(0);
x_153 = x_181;
x_154 = x_3;
x_155 = x_4;
x_156 = lean_box(0);
goto block_170;
}
block_47:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_unsigned_to_nat(7u);
x_22 = l_Lean_Syntax_getArg(x_2, x_21);
lean_dec(x_2);
x_23 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_24 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2));
lean_inc(x_22);
x_25 = l_Lean_Syntax_isOfKind(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_1);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_9);
lean_closure_set(x_27, 2, x_16);
lean_closure_set(x_27, 3, x_20);
lean_closure_set(x_27, 4, x_1);
lean_closure_set(x_27, 5, x_15);
lean_closure_set(x_27, 6, x_8);
lean_closure_set(x_27, 7, x_12);
lean_closure_set(x_27, 8, x_18);
lean_closure_set(x_27, 9, x_6);
lean_closure_set(x_27, 10, x_7);
lean_closure_set(x_27, 11, x_23);
lean_closure_set(x_27, 12, x_19);
x_28 = l_Lean_Syntax_getArg(x_22, x_12);
lean_dec(x_22);
x_29 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_30 = l_Lean_Elab_Command_expandNoKindMacroRulesAux(x_29, x_8, x_27, x_13, x_17);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_31 = lean_ctor_get(x_30, 0);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
x_32 = x_30;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
x_39 = lean_ctor_get(x_30, 0);
x_46 = !lean_is_exclusive(x_30);
if (x_46 == 0)
{
x_40 = x_30;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_30);
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
block_65:
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_unsigned_to_nat(6u);
x_58 = l_Lean_Syntax_getArg(x_2, x_57);
x_59 = l_Lean_Syntax_isNone(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_inc(x_58);
x_60 = l_Lean_Syntax_matchesNull(x_58, x_52);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_58);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_2);
lean_dec_ref(x_1);
x_61 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_Syntax_getArg(x_58, x_51);
lean_dec(x_58);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_13 = x_54;
x_14 = lean_box(0);
x_15 = x_53;
x_16 = x_48;
x_17 = x_55;
x_18 = x_49;
x_19 = x_50;
x_20 = x_63;
goto block_47;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_box(0);
x_13 = x_54;
x_14 = lean_box(0);
x_15 = x_53;
x_16 = x_48;
x_17 = x_55;
x_18 = x_49;
x_19 = x_50;
x_20 = x_64;
goto block_47;
}
}
block_96:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_unsigned_to_nat(7u);
x_77 = l_Lean_Syntax_getArg(x_2, x_76);
lean_dec(x_2);
x_78 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
x_79 = l_Lean_Name_mkStr4(x_6, x_7, x_70, x_78);
lean_inc(x_77);
x_80 = l_Lean_Syntax_isOfKind(x_77, x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_77);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
x_81 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = l_Lean_TSyntax_getId(x_68);
lean_dec(x_68);
lean_inc_ref(x_73);
x_83 = l_Lean_Elab_Command_resolveSyntaxKind(x_82, x_73, x_74);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l_Lean_Syntax_getArg(x_77, x_12);
lean_dec(x_77);
x_86 = l_Lean_Syntax_getArgs(x_85);
lean_dec(x_85);
x_87 = l_Lean_Elab_Command_elabElabRulesAux(x_71, x_67, x_66, x_84, x_69, x_72, x_86, x_73, x_74);
lean_dec(x_74);
lean_dec(x_69);
lean_dec(x_67);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_dec(x_77);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
x_88 = lean_ctor_get(x_83, 0);
x_95 = !lean_is_exclusive(x_83);
if (x_95 == 0)
{
x_89 = x_83;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_83);
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
}
block_116:
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_unsigned_to_nat(6u);
x_109 = l_Lean_Syntax_getArg(x_2, x_108);
x_110 = l_Lean_Syntax_isNone(x_109);
if (x_110 == 0)
{
uint8_t x_111; 
lean_inc(x_109);
x_111 = l_Lean_Syntax_matchesNull(x_109, x_101);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_109);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_2);
x_112 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = l_Lean_Syntax_getArg(x_109, x_99);
lean_dec(x_109);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_66 = x_97;
x_67 = x_98;
x_68 = x_100;
x_69 = x_104;
x_70 = x_102;
x_71 = x_103;
x_72 = x_114;
x_73 = x_105;
x_74 = x_106;
x_75 = lean_box(0);
goto block_96;
}
}
else
{
lean_object* x_115; 
lean_dec(x_109);
x_115 = lean_box(0);
x_66 = x_97;
x_67 = x_98;
x_68 = x_100;
x_69 = x_104;
x_70 = x_102;
x_71 = x_103;
x_72 = x_115;
x_73 = x_105;
x_74 = x_106;
x_75 = lean_box(0);
goto block_96;
}
}
block_152:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_123 = lean_unsigned_to_nat(2u);
x_124 = l_Lean_Syntax_getArg(x_2, x_123);
x_125 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_126 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(x_124);
x_127 = l_Lean_Syntax_isOfKind(x_124, x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_120);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec(x_2);
lean_dec_ref(x_1);
x_128 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_unsigned_to_nat(4u);
x_130 = l_Lean_Syntax_getArg(x_2, x_129);
lean_inc(x_130);
x_131 = l_Lean_Syntax_matchesNull(x_130, x_12);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
lean_dec_ref(x_1);
x_132 = lean_unsigned_to_nat(5u);
lean_inc(x_130);
x_133 = l_Lean_Syntax_matchesNull(x_130, x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_130);
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_120);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec(x_2);
x_134 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_135 = lean_unsigned_to_nat(3u);
x_136 = l_Lean_Syntax_getArg(x_130, x_135);
lean_dec(x_130);
x_137 = l_Lean_Syntax_getArg(x_2, x_132);
x_138 = l_Lean_Syntax_isNone(x_137);
if (x_138 == 0)
{
uint8_t x_139; 
lean_inc(x_137);
x_139 = l_Lean_Syntax_matchesNull(x_137, x_123);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_120);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec(x_2);
x_140 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = l_Lean_Syntax_getArg(x_137, x_121);
lean_dec(x_137);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_97 = x_124;
x_98 = x_122;
x_99 = x_121;
x_100 = x_136;
x_101 = x_123;
x_102 = x_125;
x_103 = x_120;
x_104 = x_142;
x_105 = x_118;
x_106 = x_117;
x_107 = lean_box(0);
goto block_116;
}
}
else
{
lean_object* x_143; 
lean_dec(x_137);
x_143 = lean_box(0);
x_97 = x_124;
x_98 = x_122;
x_99 = x_121;
x_100 = x_136;
x_101 = x_123;
x_102 = x_125;
x_103 = x_120;
x_104 = x_143;
x_105 = x_118;
x_106 = x_117;
x_107 = lean_box(0);
goto block_116;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec(x_130);
x_144 = lean_unsigned_to_nat(5u);
x_145 = l_Lean_Syntax_getArg(x_2, x_144);
x_146 = l_Lean_Syntax_isNone(x_145);
if (x_146 == 0)
{
uint8_t x_147; 
lean_inc(x_145);
x_147 = l_Lean_Syntax_matchesNull(x_145, x_123);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_145);
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_120);
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec(x_2);
lean_dec_ref(x_1);
x_148 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = l_Lean_Syntax_getArg(x_145, x_121);
lean_dec(x_145);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_48 = x_124;
x_49 = x_122;
x_50 = x_120;
x_51 = x_121;
x_52 = x_123;
x_53 = x_150;
x_54 = x_118;
x_55 = x_117;
x_56 = lean_box(0);
goto block_65;
}
}
else
{
lean_object* x_151; 
lean_dec(x_145);
x_151 = lean_box(0);
x_48 = x_124;
x_49 = x_122;
x_50 = x_120;
x_51 = x_121;
x_52 = x_123;
x_53 = x_151;
x_54 = x_118;
x_55 = x_117;
x_56 = lean_box(0);
goto block_65;
}
}
}
}
block_170:
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_unsigned_to_nat(1u);
x_158 = l_Lean_Syntax_getArg(x_2, x_157);
x_159 = l_Lean_Syntax_isNone(x_158);
if (x_159 == 0)
{
uint8_t x_160; 
lean_inc(x_158);
x_160 = l_Lean_Syntax_matchesNull(x_158, x_157);
if (x_160 == 0)
{
lean_object* x_161; 
lean_dec(x_158);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec(x_2);
lean_dec_ref(x_1);
x_161 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = l_Lean_Syntax_getArg(x_158, x_12);
lean_dec(x_158);
x_163 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(x_162);
x_164 = l_Lean_Syntax_isOfKind(x_162, x_163);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_162);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec(x_2);
lean_dec_ref(x_1);
x_165 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = l_Lean_Syntax_getArg(x_162, x_157);
lean_dec(x_162);
x_167 = l_Lean_Syntax_getArgs(x_166);
lean_dec(x_166);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_117 = x_155;
x_118 = x_154;
x_119 = lean_box(0);
x_120 = x_153;
x_121 = x_157;
x_122 = x_168;
goto block_152;
}
}
}
else
{
lean_object* x_169; 
lean_dec(x_158);
x_169 = lean_box(0);
x_117 = x_155;
x_118 = x_154;
x_119 = lean_box(0);
x_120 = x_153;
x_121 = x_157;
x_122 = x_169;
goto block_152;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabElabRules___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___closed__1));
x_6 = l_Lean_Elab_Command_adaptExpander(x_5, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabElabRules(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_4);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget_borrowed(x_3, x_2);
lean_inc_ref(x_4);
lean_inc(x_9);
x_10 = l_Lean_Elab_Command_expandMacroArg(x_9, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_18 = lean_ctor_get(x_10, 0);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
x_19 = x_10;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(x_7, x_8, x_3, x_4, x_5);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_inheritedTraceOptions;
x_5 = lean_st_ref_get(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1));
x_15 = l_Lean_Name_append(x_14, x_1);
x_16 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_5, x_10, x_15);
lean_dec(x_15);
lean_dec_ref(x_10);
lean_dec(x_5);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_54; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(x_2, x_4);
x_9 = lean_ctor_get(x_8, 0);
x_54 = !lean_is_exclusive(x_8);
if (x_54 == 0)
{
x_10 = x_8;
x_11 = x_54;
goto block_53;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_52; 
x_12 = lean_st_ref_take(x_4);
x_13 = lean_ctor_get(x_12, 9);
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 5);
x_20 = lean_ctor_get(x_12, 6);
x_21 = lean_ctor_get(x_12, 7);
x_22 = lean_ctor_get(x_12, 8);
x_23 = lean_ctor_get(x_12, 10);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
x_24 = x_12;
x_25 = x_52;
goto block_51;
}
else
{
lean_inc(x_23);
lean_inc(x_13);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_24 = lean_box(0);
x_25 = x_52;
goto block_51;
}
block_51:
{
uint64_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_50; 
x_26 = lean_ctor_get_uint64(x_13, sizeof(void*)*1);
x_27 = lean_ctor_get(x_13, 0);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
x_28 = x_13;
x_29 = x_50;
goto block_49;
}
else
{
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = x_50;
goto block_49;
}
block_49:
{
double x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0);
x_31 = 0;
x_32 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1));
x_33 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_float(x_33, sizeof(void*)*2, x_30);
lean_ctor_set_float(x_33, sizeof(void*)*2 + 8, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*2 + 16, x_31);
x_34 = lean_obj_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2);
x_35 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_9);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_PersistentArray_push___redArg(x_27, x_36);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_37);
x_38 = x_28;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set_uint64(x_48, sizeof(void*)*1, x_26);
x_38 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_39; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 9, x_38);
x_39 = x_24;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_46, 0, x_14);
lean_ctor_set(x_46, 1, x_15);
lean_ctor_set(x_46, 2, x_16);
lean_ctor_set(x_46, 3, x_17);
lean_ctor_set(x_46, 4, x_18);
lean_ctor_set(x_46, 5, x_19);
lean_ctor_set(x_46, 6, x_20);
lean_ctor_set(x_46, 7, x_21);
lean_ctor_set(x_46, 8, x_22);
lean_ctor_set(x_46, 9, x_38);
lean_ctor_set(x_46, 10, x_23);
x_39 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_st_ref_set(x_4, x_39);
x_41 = lean_box(0);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_41);
x_42 = x_10;
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
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_6, 0);
x_62 = !lean_is_exclusive(x_6);
if (x_62 == 0)
{
x_56 = x_6;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_6);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
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
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_24; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_9);
x_11 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(x_9, x_3);
x_12 = lean_ctor_get(x_11, 0);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
x_13 = x_11;
x_14 = x_24;
goto block_23;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_24;
goto block_23;
}
block_23:
{
uint8_t x_15; 
x_15 = lean_unbox(x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_del_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
x_1 = x_8;
goto _start;
}
else
{
lean_object* x_17; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_10);
x_17 = x_13;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_10);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_MessageData_ofFormat(x_17);
x_19 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(x_9, x_18, x_2, x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_19);
x_1 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
return x_19;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = 0;
x_6 = l_Lean_Environment_setExporting(x_1, x_5);
lean_inc(x_2);
x_7 = l_Lean_mkPrivateName(x_6, x_2);
x_8 = 1;
lean_inc_ref(x_6);
x_9 = l_Lean_Environment_contains(x_6, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_privateToUserName(x_2);
x_11 = l_Lean_Environment_contains(x_6, x_10, x_8);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_14 = lean_box(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_8 = x_5;
x_9 = x_15;
goto block_14;
}
else
{
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_7);
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
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_45; 
x_17 = lean_ctor_get(x_6, 0);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
x_18 = x_6;
x_19 = x_45;
goto block_44;
}
else
{
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
lean_del_object(x_18);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec_ref(x_5);
x_22 = lean_ctor_get(x_20, 0);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
x_23 = x_20;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(x_25, x_21);
lean_dec_ref(x_25);
return x_26;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_43; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec_ref(x_5);
x_32 = lean_ctor_get(x_20, 0);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
x_33 = x_20;
x_34 = x_43;
goto block_42;
}
else
{
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_box(0);
x_34 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_35; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_32);
x_35 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_32);
x_35 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_36; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_35);
x_36 = x_33;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_35);
x_36 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_37; 
x_37 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(x_36, x_31);
lean_dec_ref(x_36);
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
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
x_48 = x_5;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
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
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqExtraModUse_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqExtraModUse_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableExtraModUse_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1));
x_2 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0));
x_3 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_45; uint8_t x_46; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
lean_dec_ref(x_8);
x_10 = lean_st_ref_get(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2);
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*1 + 1, x_2);
x_14 = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
x_15 = lean_box(1);
x_16 = lean_box(0);
x_45 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_12, x_14, x_11, x_15, x_16);
x_46 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(x_45, x_13);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_55; lean_object* x_56; uint8_t x_69; 
x_47 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4));
x_48 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(x_47, x_5);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_69 = lean_unbox(x_49);
lean_dec(x_49);
if (x_69 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
x_17 = x_5;
x_18 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11);
if (x_9 == 0)
{
lean_object* x_79; 
x_79 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16));
x_71 = x_79;
goto block_78;
}
else
{
lean_object* x_80; 
x_80 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17));
x_71 = x_80;
goto block_78;
}
block_78:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = l_Lean_stringToMessageData(x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
if (x_2 == 0)
{
lean_object* x_76; 
x_76 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14));
x_55 = x_75;
x_56 = x_76;
goto block_68;
}
else
{
lean_object* x_77; 
x_77 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15));
x_55 = x_75;
x_56 = x_77;
goto block_68;
}
}
}
block_54:
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(x_47, x_52, x_4, x_5);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
x_17 = x_5;
x_18 = lean_box(0);
goto block_44;
}
else
{
lean_dec_ref(x_13);
return x_53;
}
}
block_68:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_57 = l_Lean_stringToMessageData(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_MessageData_ofName(x_1);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Name_isAnonymous(x_3);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8);
x_65 = l_Lean_MessageData_ofName(x_3);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_50 = x_62;
x_51 = x_66;
goto block_54;
}
else
{
lean_object* x_67; 
lean_dec(x_3);
x_67 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9);
x_50 = x_62;
x_51 = x_67;
goto block_54;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
block_44:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_43; 
x_19 = lean_st_ref_take(x_17);
x_20 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_19, 2);
x_24 = lean_ctor_get(x_19, 3);
x_25 = lean_ctor_get(x_19, 4);
x_26 = lean_ctor_get(x_19, 5);
x_27 = lean_ctor_get(x_19, 6);
x_28 = lean_ctor_get(x_19, 7);
x_29 = lean_ctor_get(x_19, 8);
x_30 = lean_ctor_get(x_19, 9);
x_31 = lean_ctor_get(x_19, 10);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
x_32 = x_19;
x_33 = x_43;
goto block_42;
}
else
{
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_32 = lean_box(0);
x_33 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 2);
lean_inc(x_34);
lean_dec_ref(x_20);
x_35 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_14, x_21, x_13, x_34, x_16);
lean_dec(x_34);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_35);
x_36 = x_32;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_22);
lean_ctor_set(x_41, 2, x_23);
lean_ctor_set(x_41, 3, x_24);
lean_ctor_set(x_41, 4, x_25);
lean_ctor_set(x_41, 5, x_26);
lean_ctor_set(x_41, 6, x_27);
lean_ctor_set(x_41, 7, x_28);
lean_ctor_set(x_41, 8, x_29);
lean_ctor_set(x_41, 9, x_30);
lean_ctor_set(x_41, 10, x_31);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_st_ref_set(x_17, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(x_1, x_7, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_12 = l_Lean_Environment_header(x_1);
x_13 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_instInhabitedEffectiveImport_default;
x_15 = lean_array_uget_borrowed(x_3, x_5);
x_16 = lean_array_get(x_14, x_13, x_15);
lean_dec_ref(x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = 0;
lean_inc(x_2);
x_20 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(x_18, x_19, x_2, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_dec_ref(x_20);
x_21 = lean_box(0);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_6 = x_21;
goto _start;
}
else
{
lean_dec(x_2);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0);
x_5 = x_20;
goto block_19;
}
else
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_5 = x_21;
goto block_19;
}
block_19:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(x_2, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1));
x_2 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0));
x_3 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_26; 
x_6 = lean_st_ref_get(x_4);
x_10 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_10);
lean_dec(x_6);
x_26 = l_Lean_Environment_getModuleIdxFor_x3f(x_10, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_10);
lean_dec(x_1);
goto block_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_Environment_header(x_10);
x_29 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_29);
lean_dec_ref(x_28);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_27, x_30);
if (x_31 == 0)
{
lean_dec_ref(x_29);
lean_dec(x_27);
lean_dec_ref(x_10);
lean_dec(x_1);
goto block_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_st_ref_get(x_4);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
lean_dec(x_32);
x_34 = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2);
x_35 = lean_array_fget(x_29, x_27);
lean_dec(x_27);
lean_dec_ref(x_29);
if (x_2 == 0)
{
lean_dec_ref(x_33);
x_36 = x_2;
goto block_47;
}
else
{
uint8_t x_48; 
lean_inc(x_1);
x_48 = l_Lean_isMarkedMeta(x_33, x_1);
if (x_48 == 0)
{
x_36 = x_2;
goto block_47;
}
else
{
uint8_t x_49; 
x_49 = 0;
x_36 = x_49;
goto block_47;
}
}
block_47:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_1);
x_39 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(x_38, x_36, x_1, x_3, x_4);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_39);
x_40 = l_Lean_indirectModUseExt;
x_41 = lean_box(1);
x_42 = lean_box(0);
lean_inc_ref(x_10);
x_43 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_34, x_40, x_10, x_41, x_42);
x_44 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(x_43, x_1);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3);
x_11 = lean_box(0);
x_12 = x_45;
goto block_25;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec_ref(x_44);
x_11 = lean_box(0);
x_12 = x_46;
goto block_25;
}
}
else
{
lean_dec_ref(x_10);
lean_dec(x_1);
return x_39;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_25:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = lean_array_size(x_12);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(x_10, x_1, x_12, x_14, x_15, x_13, x_3, x_4);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_17 = x_16;
x_18 = x_23;
goto block_22;
}
else
{
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_13);
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_13);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(x_1, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = 1;
x_10 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(x_7, x_9, x_3, x_4);
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
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4);
x_2 = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2));
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Command_instInhabitedScope_default;
x_10 = l_List_head_x21___redArg(x_9, x_8);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Command_getScope___redArg(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Command_getScope___redArg(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_24, 0, x_6);
lean_inc_ref(x_6);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_25, 0, x_6);
lean_inc(x_14);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(x_26, 0, x_14);
lean_inc(x_17);
lean_inc(x_14);
lean_inc_ref(x_6);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(x_27, 0, x_6);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_17);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(x_28, 0, x_6);
lean_closure_set(x_28, 1, x_11);
lean_closure_set(x_28, 2, x_14);
lean_closure_set(x_28, 3, x_17);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_3);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_30 = x_105;
x_31 = lean_box(0);
goto block_103;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_23, 0);
lean_inc(x_106);
x_30 = x_106;
x_31 = lean_box(0);
goto block_103;
}
block_103:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_st_ref_get(x_3);
x_33 = lean_ctor_get(x_32, 5);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_get(x_3);
x_35 = lean_ctor_get(x_34, 4);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_22);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_21);
lean_ctor_set(x_36, 3, x_22);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_19);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_apply_2(x_1, x_36, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(x_44, x_45, x_2, x_3);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_83; 
lean_dec_ref(x_46);
x_47 = lean_st_ref_take(x_3);
x_48 = lean_ctor_get(x_47, 0);
x_49 = lean_ctor_get(x_47, 1);
x_50 = lean_ctor_get(x_47, 2);
x_51 = lean_ctor_get(x_47, 3);
x_52 = lean_ctor_get(x_47, 5);
x_53 = lean_ctor_get(x_47, 6);
x_54 = lean_ctor_get(x_47, 7);
x_55 = lean_ctor_get(x_47, 8);
x_56 = lean_ctor_get(x_47, 9);
x_57 = lean_ctor_get(x_47, 10);
x_83 = !lean_is_exclusive(x_47);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_47, 4);
lean_dec(x_84);
x_58 = x_47;
x_59 = x_83;
goto block_82;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_47);
x_58 = lean_box(0);
x_59 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_60; 
if (x_59 == 0)
{
lean_ctor_set(x_58, 4, x_42);
x_60 = x_58;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_81, 0, x_48);
lean_ctor_set(x_81, 1, x_49);
lean_ctor_set(x_81, 2, x_50);
lean_ctor_set(x_81, 3, x_51);
lean_ctor_set(x_81, 4, x_42);
lean_ctor_set(x_81, 5, x_52);
lean_ctor_set(x_81, 6, x_53);
lean_ctor_set(x_81, 7, x_54);
lean_ctor_set(x_81, 8, x_55);
lean_ctor_set(x_81, 9, x_56);
lean_ctor_set(x_81, 10, x_57);
x_60 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_st_ref_set(x_3, x_60);
x_62 = l_List_reverse___redArg(x_43);
x_63 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(x_62, x_2, x_3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; uint8_t x_70; 
x_70 = !lean_is_exclusive(x_63);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_63, 0);
lean_dec(x_71);
x_64 = x_63;
x_65 = x_70;
goto block_69;
}
else
{
lean_dec(x_63);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
lean_ctor_set(x_64, 0, x_41);
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_41);
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
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_41);
x_72 = lean_ctor_get(x_63, 0);
x_79 = !lean_is_exclusive(x_63);
if (x_79 == 0)
{
x_73 = x_63;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_63);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_2);
x_85 = lean_ctor_get(x_46, 0);
x_92 = !lean_is_exclusive(x_46);
if (x_92 == 0)
{
x_86 = x_46;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_46);
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
else
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_39, 0);
lean_inc(x_93);
lean_dec_ref(x_39);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc_ref(x_95);
lean_dec_ref(x_93);
x_96 = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
x_97 = lean_string_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_95);
x_99 = l_Lean_MessageData_ofFormat(x_98);
x_100 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_94, x_99, x_2, x_3);
lean_dec(x_94);
return x_100;
}
else
{
lean_object* x_101; 
lean_dec_ref(x_95);
lean_dec_ref(x_2);
x_101 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(x_94);
return x_101;
}
}
else
{
lean_object* x_102; 
lean_dec_ref(x_2);
x_102 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_102;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_114; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_107 = lean_ctor_get(x_20, 0);
x_114 = !lean_is_exclusive(x_20);
if (x_114 == 0)
{
x_108 = x_20;
x_109 = x_114;
goto block_113;
}
else
{
lean_inc(x_107);
lean_dec(x_20);
x_108 = lean_box(0);
x_109 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_110; 
if (x_109 == 0)
{
x_110 = x_108;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_107);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_122; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_115 = lean_ctor_get(x_18, 0);
x_122 = !lean_is_exclusive(x_18);
if (x_122 == 0)
{
x_116 = x_18;
x_117 = x_122;
goto block_121;
}
else
{
lean_inc(x_115);
lean_dec(x_18);
x_116 = lean_box(0);
x_117 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_118; 
if (x_117 == 0)
{
x_118 = x_116;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_115);
x_118 = x_120;
goto block_119;
}
block_119:
{
return x_118;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_130; 
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_123 = lean_ctor_get(x_15, 0);
x_130 = !lean_is_exclusive(x_15);
if (x_130 == 0)
{
x_124 = x_15;
x_125 = x_130;
goto block_129;
}
else
{
lean_inc(x_123);
lean_dec(x_15);
x_124 = lean_box(0);
x_125 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_126; 
if (x_125 == 0)
{
x_126 = x_124;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_123);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_138; 
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_131 = lean_ctor_get(x_12, 0);
x_138 = !lean_is_exclusive(x_12);
if (x_138 == 0)
{
x_132 = x_12;
x_133 = x_138;
goto block_137;
}
else
{
lean_inc(x_131);
lean_dec(x_12);
x_132 = lean_box(0);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_133 == 0)
{
x_134 = x_132;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_131);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_48; uint8_t x_49; 
x_5 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_6 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_48 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(x_1);
x_49 = l_Lean_Syntax_isOfKind(x_1, x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_50 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; size_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; size_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; size_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; size_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_540; uint8_t x_541; 
x_51 = lean_unsigned_to_nat(0u);
x_540 = l_Lean_Syntax_getArg(x_1, x_51);
x_541 = l_Lean_Syntax_isNone(x_540);
if (x_541 == 0)
{
lean_object* x_542; uint8_t x_543; 
x_542 = lean_unsigned_to_nat(1u);
lean_inc(x_540);
x_543 = l_Lean_Syntax_matchesNull(x_540, x_542);
if (x_543 == 0)
{
lean_object* x_544; 
lean_dec(x_540);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_544 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_544;
}
else
{
lean_object* x_545; lean_object* x_546; uint8_t x_547; 
x_545 = l_Lean_Syntax_getArg(x_540, x_51);
lean_dec(x_540);
x_546 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(x_545);
x_547 = l_Lean_Syntax_isOfKind(x_545, x_546);
if (x_547 == 0)
{
lean_object* x_548; 
lean_dec(x_545);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_548 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_548;
}
else
{
lean_object* x_549; 
x_549 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_549, 0, x_545);
x_522 = x_549;
x_523 = x_2;
x_524 = x_3;
x_525 = lean_box(0);
goto block_539;
}
}
}
else
{
lean_object* x_550; 
lean_dec(x_540);
x_550 = lean_box(0);
x_522 = x_550;
x_523 = x_2;
x_524 = x_3;
x_525 = lean_box(0);
goto block_539;
}
block_81:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_inc_ref(x_67);
x_69 = l_Array_append___redArg(x_67, x_68);
lean_dec_ref(x_68);
lean_inc(x_59);
lean_inc(x_64);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_59);
lean_ctor_set(x_70, 2, x_69);
lean_inc_ref(x_67);
lean_inc(x_59);
lean_inc(x_64);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_59);
lean_ctor_set(x_71, 2, x_67);
lean_inc_ref(x_71);
lean_inc(x_64);
x_72 = l_Lean_Syntax_node1(x_64, x_66, x_71);
lean_inc(x_64);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_60);
lean_inc(x_64);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_54);
lean_inc(x_59);
lean_inc(x_64);
x_75 = l_Lean_Syntax_node2(x_64, x_59, x_74, x_55);
if (lean_obj_tag(x_58) == 1)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_58, 0);
lean_inc(x_76);
lean_dec_ref(x_58);
x_77 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(x_64);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_64);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Array_mkArray2___redArg(x_78, x_76);
x_7 = x_52;
x_8 = x_75;
x_9 = x_53;
x_10 = x_56;
x_11 = x_73;
x_12 = x_72;
x_13 = lean_box(0);
x_14 = x_59;
x_15 = x_61;
x_16 = x_62;
x_17 = x_63;
x_18 = x_64;
x_19 = x_70;
x_20 = x_65;
x_21 = x_67;
x_22 = x_71;
x_23 = x_79;
goto block_47;
}
else
{
lean_object* x_80; 
lean_dec(x_58);
x_80 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_7 = x_52;
x_8 = x_75;
x_9 = x_53;
x_10 = x_56;
x_11 = x_73;
x_12 = x_72;
x_13 = lean_box(0);
x_14 = x_59;
x_15 = x_61;
x_16 = x_62;
x_17 = x_63;
x_18 = x_64;
x_19 = x_70;
x_20 = x_65;
x_21 = x_67;
x_22 = x_71;
x_23 = x_80;
goto block_47;
}
}
block_102:
{
lean_object* x_97; lean_object* x_98; 
x_97 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
x_98 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
if (lean_obj_tag(x_87) == 1)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_87, 0);
lean_inc(x_99);
lean_dec_ref(x_87);
x_100 = l_Array_mkArray1___redArg(x_99);
x_52 = x_82;
x_53 = x_83;
x_54 = x_84;
x_55 = x_85;
x_56 = x_86;
x_57 = lean_box(0);
x_58 = x_88;
x_59 = x_89;
x_60 = x_97;
x_61 = x_98;
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_94;
x_67 = x_95;
x_68 = x_100;
goto block_81;
}
else
{
lean_object* x_101; 
lean_dec(x_87);
x_101 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_52 = x_82;
x_53 = x_83;
x_54 = x_84;
x_55 = x_85;
x_56 = x_86;
x_57 = lean_box(0);
x_58 = x_88;
x_59 = x_89;
x_60 = x_97;
x_61 = x_98;
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_94;
x_67 = x_95;
x_68 = x_101;
goto block_81;
}
}
block_194:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; size_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_inc_ref(x_123);
x_127 = l_Array_append___redArg(x_123, x_126);
lean_dec_ref(x_126);
lean_inc(x_114);
lean_inc(x_109);
x_128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_128, 0, x_109);
lean_ctor_set(x_128, 1, x_114);
lean_ctor_set(x_128, 2, x_127);
x_129 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
x_130 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc(x_109);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_109);
lean_ctor_set(x_131, 1, x_130);
x_132 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
lean_inc(x_109);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_109);
lean_ctor_set(x_133, 1, x_132);
x_134 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_109);
x_135 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_135, 0, x_109);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Nat_reprFast(x_107);
x_137 = lean_box(2);
x_138 = l_Lean_Syntax_mkNumLit(x_136, x_137);
x_139 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
lean_inc(x_109);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_109);
lean_ctor_set(x_140, 1, x_139);
lean_inc(x_109);
x_141 = l_Lean_Syntax_node5(x_109, x_129, x_131, x_133, x_135, x_138, x_140);
lean_inc(x_114);
lean_inc(x_109);
x_142 = l_Lean_Syntax_node1(x_109, x_114, x_141);
x_143 = lean_array_size(x_120);
x_144 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(x_143, x_110, x_120);
lean_inc_ref(x_123);
x_145 = l_Array_append___redArg(x_123, x_144);
lean_dec_ref(x_144);
lean_inc(x_114);
lean_inc(x_109);
x_146 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_146, 0, x_109);
lean_ctor_set(x_146, 1, x_114);
lean_ctor_set(x_146, 2, x_145);
x_147 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_109);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_109);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_obj_once(&l_Lean_Elab_Command_elabElab___closed__7, &l_Lean_Elab_Command_elabElab___closed__7_once, _init_l_Lean_Elab_Command_elabElab___closed__7);
x_150 = lean_array_push(x_149, x_124);
x_151 = lean_array_push(x_150, x_118);
x_152 = lean_array_push(x_151, x_104);
x_153 = lean_array_push(x_152, x_113);
x_154 = lean_array_push(x_153, x_106);
x_155 = lean_array_push(x_154, x_128);
x_156 = lean_array_push(x_155, x_142);
x_157 = lean_array_push(x_156, x_146);
x_158 = lean_array_push(x_157, x_148);
lean_inc(x_105);
x_159 = lean_array_push(x_158, x_105);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_109);
lean_ctor_set(x_160, 1, x_116);
lean_ctor_set(x_160, 2, x_159);
lean_inc(x_117);
lean_inc_ref(x_103);
x_161 = l_Lean_Elab_Command_elabSyntax(x_160, x_103, x_117);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec_ref(x_161);
x_163 = l_Lean_Elab_Command_getRef___redArg(x_103);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_103);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_165);
x_166 = lean_ctor_get(x_103, 5);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_137);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_125);
x_168 = l_Lean_SourceInfo_fromRef(x_164, x_122);
lean_dec(x_164);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_169; 
x_169 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_117);
lean_dec_ref(x_169);
x_82 = x_103;
x_83 = x_139;
x_84 = x_147;
x_85 = x_105;
x_86 = x_167;
x_87 = x_108;
x_88 = x_112;
x_89 = x_114;
x_90 = x_115;
x_91 = x_117;
x_92 = x_168;
x_93 = x_119;
x_94 = x_121;
x_95 = x_123;
x_96 = lean_box(0);
goto block_102;
}
else
{
x_82 = x_103;
x_83 = x_139;
x_84 = x_147;
x_85 = x_105;
x_86 = x_167;
x_87 = x_108;
x_88 = x_112;
x_89 = x_114;
x_90 = x_115;
x_91 = x_117;
x_92 = x_168;
x_93 = x_119;
x_94 = x_121;
x_95 = x_123;
x_96 = lean_box(0);
goto block_102;
}
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_177; 
lean_dec(x_164);
lean_dec(x_162);
lean_dec_ref(x_125);
lean_dec_ref(x_123);
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_117);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_105);
lean_dec_ref(x_103);
x_170 = lean_ctor_get(x_165, 0);
x_177 = !lean_is_exclusive(x_165);
if (x_177 == 0)
{
x_171 = x_165;
x_172 = x_177;
goto block_176;
}
else
{
lean_inc(x_170);
lean_dec(x_165);
x_171 = lean_box(0);
x_172 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_173; 
if (x_172 == 0)
{
x_173 = x_171;
goto block_174;
}
else
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_170);
x_173 = x_175;
goto block_174;
}
block_174:
{
return x_173;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_185; 
lean_dec(x_162);
lean_dec_ref(x_125);
lean_dec_ref(x_123);
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_117);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_105);
lean_dec_ref(x_103);
x_178 = lean_ctor_get(x_163, 0);
x_185 = !lean_is_exclusive(x_163);
if (x_185 == 0)
{
x_179 = x_163;
x_180 = x_185;
goto block_184;
}
else
{
lean_inc(x_178);
lean_dec(x_163);
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
lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_193; 
lean_dec_ref(x_125);
lean_dec_ref(x_123);
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_117);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_105);
lean_dec_ref(x_103);
x_186 = lean_ctor_get(x_161, 0);
x_193 = !lean_is_exclusive(x_161);
if (x_193 == 0)
{
x_187 = x_161;
x_188 = x_193;
goto block_192;
}
else
{
lean_inc(x_186);
lean_dec(x_161);
x_187 = lean_box(0);
x_188 = x_193;
goto block_192;
}
block_192:
{
lean_object* x_189; 
if (x_188 == 0)
{
x_189 = x_187;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_186);
x_189 = x_191;
goto block_190;
}
block_190:
{
return x_189;
}
}
}
}
block_234:
{
lean_object* x_219; lean_object* x_220; 
lean_inc_ref(x_215);
x_219 = l_Array_append___redArg(x_215, x_218);
lean_dec_ref(x_218);
lean_inc(x_205);
lean_inc(x_200);
x_220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_220, 0, x_200);
lean_ctor_set(x_220, 1, x_205);
lean_ctor_set(x_220, 2, x_219);
if (lean_obj_tag(x_214) == 1)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_221 = lean_ctor_get(x_214, 0);
lean_inc(x_221);
lean_dec_ref(x_214);
x_222 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
x_223 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc(x_200);
x_224 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_224, 0, x_200);
lean_ctor_set(x_224, 1, x_223);
x_225 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__10));
lean_inc(x_200);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_200);
lean_ctor_set(x_226, 1, x_225);
x_227 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_200);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_200);
lean_ctor_set(x_228, 1, x_227);
x_229 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
lean_inc(x_200);
x_230 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_230, 0, x_200);
lean_ctor_set(x_230, 1, x_229);
lean_inc(x_200);
x_231 = l_Lean_Syntax_node5(x_200, x_222, x_224, x_226, x_228, x_221, x_230);
x_232 = l_Array_mkArray1___redArg(x_231);
x_103 = x_195;
x_104 = x_196;
x_105 = x_197;
x_106 = x_220;
x_107 = x_198;
x_108 = x_199;
x_109 = x_200;
x_110 = x_201;
x_111 = lean_box(0);
x_112 = x_203;
x_113 = x_204;
x_114 = x_205;
x_115 = x_206;
x_116 = x_207;
x_117 = x_208;
x_118 = x_209;
x_119 = x_211;
x_120 = x_210;
x_121 = x_212;
x_122 = x_213;
x_123 = x_215;
x_124 = x_216;
x_125 = x_217;
x_126 = x_232;
goto block_194;
}
else
{
lean_object* x_233; 
lean_dec(x_214);
x_233 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_103 = x_195;
x_104 = x_196;
x_105 = x_197;
x_106 = x_220;
x_107 = x_198;
x_108 = x_199;
x_109 = x_200;
x_110 = x_201;
x_111 = lean_box(0);
x_112 = x_203;
x_113 = x_204;
x_114 = x_205;
x_115 = x_206;
x_116 = x_207;
x_117 = x_208;
x_118 = x_209;
x_119 = x_211;
x_120 = x_210;
x_121 = x_212;
x_122 = x_213;
x_123 = x_215;
x_124 = x_216;
x_125 = x_217;
x_126 = x_233;
goto block_194;
}
}
block_271:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_inc_ref(x_256);
x_260 = l_Array_append___redArg(x_256, x_259);
lean_dec_ref(x_259);
lean_inc(x_246);
lean_inc(x_242);
x_261 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_261, 0, x_242);
lean_ctor_set(x_261, 1, x_246);
lean_ctor_set(x_261, 2, x_260);
x_262 = l_Lean_SourceInfo_fromRef(x_252, x_49);
lean_dec(x_252);
x_263 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_236);
if (lean_obj_tag(x_235) == 1)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_264 = lean_ctor_get(x_235, 0);
lean_inc(x_264);
lean_dec_ref(x_235);
x_265 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
x_266 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_242);
x_267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_267, 0, x_242);
lean_ctor_set(x_267, 1, x_266);
lean_inc(x_242);
x_268 = l_Lean_Syntax_node2(x_242, x_265, x_267, x_264);
x_269 = l_Array_mkArray1___redArg(x_268);
x_195 = x_237;
x_196 = x_238;
x_197 = x_239;
x_198 = x_240;
x_199 = x_241;
x_200 = x_242;
x_201 = x_243;
x_202 = lean_box(0);
x_203 = x_245;
x_204 = x_263;
x_205 = x_246;
x_206 = x_247;
x_207 = x_248;
x_208 = x_249;
x_209 = x_261;
x_210 = x_251;
x_211 = x_250;
x_212 = x_253;
x_213 = x_254;
x_214 = x_255;
x_215 = x_256;
x_216 = x_257;
x_217 = x_258;
x_218 = x_269;
goto block_234;
}
else
{
lean_object* x_270; 
lean_dec(x_235);
x_270 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_195 = x_237;
x_196 = x_238;
x_197 = x_239;
x_198 = x_240;
x_199 = x_241;
x_200 = x_242;
x_201 = x_243;
x_202 = lean_box(0);
x_203 = x_245;
x_204 = x_263;
x_205 = x_246;
x_206 = x_247;
x_207 = x_248;
x_208 = x_249;
x_209 = x_261;
x_210 = x_251;
x_211 = x_250;
x_212 = x_253;
x_213 = x_254;
x_214 = x_255;
x_215 = x_256;
x_216 = x_257;
x_217 = x_258;
x_218 = x_270;
goto block_234;
}
}
block_311:
{
lean_object* x_297; lean_object* x_298; 
lean_inc_ref(x_294);
x_297 = l_Array_append___redArg(x_294, x_296);
lean_dec_ref(x_296);
lean_inc(x_284);
lean_inc(x_280);
x_298 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_298, 0, x_280);
lean_ctor_set(x_298, 1, x_284);
lean_ctor_set(x_298, 2, x_297);
if (lean_obj_tag(x_277) == 1)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_299 = lean_ctor_get(x_277, 0);
lean_inc(x_299);
lean_dec_ref(x_277);
x_300 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_285);
x_301 = l_Lean_Name_mkStr4(x_5, x_6, x_285, x_300);
x_302 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_280);
x_303 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_303, 0, x_280);
lean_ctor_set(x_303, 1, x_302);
lean_inc_ref(x_294);
x_304 = l_Array_append___redArg(x_294, x_299);
lean_dec(x_299);
lean_inc(x_284);
lean_inc(x_280);
x_305 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_305, 0, x_280);
lean_ctor_set(x_305, 1, x_284);
lean_ctor_set(x_305, 2, x_304);
x_306 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_280);
x_307 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_307, 0, x_280);
lean_ctor_set(x_307, 1, x_306);
lean_inc(x_280);
x_308 = l_Lean_Syntax_node3(x_280, x_301, x_303, x_305, x_307);
x_309 = l_Array_mkArray1___redArg(x_308);
x_235 = x_272;
x_236 = x_273;
x_237 = x_274;
x_238 = x_275;
x_239 = x_276;
x_240 = x_278;
x_241 = x_279;
x_242 = x_280;
x_243 = x_281;
x_244 = lean_box(0);
x_245 = x_283;
x_246 = x_284;
x_247 = x_285;
x_248 = x_286;
x_249 = x_287;
x_250 = x_289;
x_251 = x_288;
x_252 = x_290;
x_253 = x_291;
x_254 = x_292;
x_255 = x_293;
x_256 = x_294;
x_257 = x_298;
x_258 = x_295;
x_259 = x_309;
goto block_271;
}
else
{
lean_object* x_310; 
lean_dec(x_277);
x_310 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_235 = x_272;
x_236 = x_273;
x_237 = x_274;
x_238 = x_275;
x_239 = x_276;
x_240 = x_278;
x_241 = x_279;
x_242 = x_280;
x_243 = x_281;
x_244 = lean_box(0);
x_245 = x_283;
x_246 = x_284;
x_247 = x_285;
x_248 = x_286;
x_249 = x_287;
x_250 = x_289;
x_251 = x_288;
x_252 = x_290;
x_253 = x_291;
x_254 = x_292;
x_255 = x_293;
x_256 = x_294;
x_257 = x_298;
x_258 = x_295;
x_259 = x_310;
goto block_271;
}
}
block_339:
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
x_333 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__14));
x_334 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_335 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_318) == 1)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_318, 0);
lean_inc(x_336);
x_337 = l_Array_mkArray1___redArg(x_336);
x_272 = x_312;
x_273 = x_332;
x_274 = x_313;
x_275 = x_314;
x_276 = x_315;
x_277 = x_316;
x_278 = x_317;
x_279 = x_318;
x_280 = x_319;
x_281 = x_320;
x_282 = lean_box(0);
x_283 = x_321;
x_284 = x_334;
x_285 = x_322;
x_286 = x_333;
x_287 = x_323;
x_288 = x_325;
x_289 = x_324;
x_290 = x_326;
x_291 = x_327;
x_292 = x_328;
x_293 = x_329;
x_294 = x_335;
x_295 = x_330;
x_296 = x_337;
goto block_311;
}
else
{
lean_object* x_338; 
x_338 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__33, &l_Lean_Elab_Command_elabElabRulesAux___closed__33_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__33);
x_272 = x_312;
x_273 = x_332;
x_274 = x_313;
x_275 = x_314;
x_276 = x_315;
x_277 = x_316;
x_278 = x_317;
x_279 = x_318;
x_280 = x_319;
x_281 = x_320;
x_282 = lean_box(0);
x_283 = x_321;
x_284 = x_334;
x_285 = x_322;
x_286 = x_333;
x_287 = x_323;
x_288 = x_325;
x_289 = x_324;
x_290 = x_326;
x_291 = x_327;
x_292 = x_328;
x_293 = x_329;
x_294 = x_335;
x_295 = x_330;
x_296 = x_338;
goto block_311;
}
}
block_408:
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_alloc_closure((void*)(l_Lean_evalOptPrio), 3, 1);
lean_closure_set(x_357, 0, x_340);
lean_inc_ref(x_354);
x_358 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(x_357, x_354, x_355);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; size_t x_361; size_t x_362; lean_object* x_363; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
lean_dec_ref(x_358);
x_360 = l_Lean_Syntax_getArgs(x_347);
lean_dec(x_347);
x_361 = lean_array_size(x_360);
x_362 = 0;
lean_inc_ref(x_354);
x_363 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(x_361, x_362, x_360, x_354, x_355);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
lean_dec_ref(x_363);
x_365 = l_Array_unzip___redArg(x_364);
lean_dec(x_364);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec_ref(x_365);
x_368 = l_Lean_Elab_Command_getRef___redArg(x_354);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
lean_dec_ref(x_368);
x_370 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_354);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; 
lean_dec_ref(x_370);
x_371 = lean_ctor_get(x_354, 5);
x_372 = l_Lean_Syntax_getArg(x_345, x_349);
lean_dec(x_345);
x_373 = 0;
x_374 = l_Lean_SourceInfo_fromRef(x_369, x_373);
lean_dec(x_369);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_375; 
x_375 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_355);
lean_dec_ref(x_375);
x_312 = x_341;
x_313 = x_354;
x_314 = x_342;
x_315 = x_343;
x_316 = x_344;
x_317 = x_359;
x_318 = x_346;
x_319 = x_374;
x_320 = x_362;
x_321 = x_353;
x_322 = x_348;
x_323 = x_355;
x_324 = x_372;
x_325 = x_366;
x_326 = x_350;
x_327 = x_351;
x_328 = x_373;
x_329 = x_352;
x_330 = x_367;
x_331 = lean_box(0);
goto block_339;
}
else
{
x_312 = x_341;
x_313 = x_354;
x_314 = x_342;
x_315 = x_343;
x_316 = x_344;
x_317 = x_359;
x_318 = x_346;
x_319 = x_374;
x_320 = x_362;
x_321 = x_353;
x_322 = x_348;
x_323 = x_355;
x_324 = x_372;
x_325 = x_366;
x_326 = x_350;
x_327 = x_351;
x_328 = x_373;
x_329 = x_352;
x_330 = x_367;
x_331 = lean_box(0);
goto block_339;
}
}
else
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; uint8_t x_383; 
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_359);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec_ref(x_348);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
x_376 = lean_ctor_get(x_370, 0);
x_383 = !lean_is_exclusive(x_370);
if (x_383 == 0)
{
x_377 = x_370;
x_378 = x_383;
goto block_382;
}
else
{
lean_inc(x_376);
lean_dec(x_370);
x_377 = lean_box(0);
x_378 = x_383;
goto block_382;
}
block_382:
{
lean_object* x_379; 
if (x_378 == 0)
{
x_379 = x_377;
goto block_380;
}
else
{
lean_object* x_381; 
x_381 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_381, 0, x_376);
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
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_359);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec_ref(x_348);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
x_384 = lean_ctor_get(x_368, 0);
x_391 = !lean_is_exclusive(x_368);
if (x_391 == 0)
{
x_385 = x_368;
x_386 = x_391;
goto block_390;
}
else
{
lean_inc(x_384);
lean_dec(x_368);
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
else
{
lean_object* x_392; lean_object* x_393; uint8_t x_394; uint8_t x_399; 
lean_dec(x_359);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec_ref(x_348);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
x_392 = lean_ctor_get(x_363, 0);
x_399 = !lean_is_exclusive(x_363);
if (x_399 == 0)
{
x_393 = x_363;
x_394 = x_399;
goto block_398;
}
else
{
lean_inc(x_392);
lean_dec(x_363);
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
else
{
lean_object* x_400; lean_object* x_401; uint8_t x_402; uint8_t x_407; 
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec_ref(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
x_400 = lean_ctor_get(x_358, 0);
x_407 = !lean_is_exclusive(x_358);
if (x_407 == 0)
{
x_401 = x_358;
x_402 = x_407;
goto block_406;
}
else
{
lean_inc(x_400);
lean_dec(x_358);
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
block_439:
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
x_424 = lean_unsigned_to_nat(8u);
x_425 = l_Lean_Syntax_getArg(x_1, x_424);
x_426 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__16));
lean_inc(x_425);
x_427 = l_Lean_Syntax_isOfKind(x_425, x_426);
if (x_427 == 0)
{
lean_object* x_428; 
lean_dec(x_425);
lean_dec(x_422);
lean_dec_ref(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_413);
lean_dec_ref(x_410);
lean_dec(x_409);
lean_dec(x_1);
x_428 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_428;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_429 = lean_unsigned_to_nat(7u);
x_430 = l_Lean_Syntax_getArg(x_1, x_429);
lean_dec(x_1);
x_431 = l_Lean_Syntax_getArg(x_425, x_414);
x_432 = l_Lean_Syntax_getArg(x_425, x_411);
x_433 = l_Lean_Syntax_isNone(x_432);
if (x_433 == 0)
{
uint8_t x_434; 
lean_inc(x_432);
x_434 = l_Lean_Syntax_matchesNull(x_432, x_411);
if (x_434 == 0)
{
lean_object* x_435; 
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_425);
lean_dec(x_422);
lean_dec_ref(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_413);
lean_dec_ref(x_410);
lean_dec(x_409);
x_435 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; 
x_436 = l_Lean_Syntax_getArg(x_432, x_414);
lean_dec(x_432);
x_437 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_437, 0, x_436);
x_340 = x_420;
x_341 = x_409;
x_342 = x_413;
x_343 = x_431;
x_344 = x_416;
x_345 = x_425;
x_346 = x_418;
x_347 = x_430;
x_348 = x_410;
x_349 = x_412;
x_350 = x_415;
x_351 = x_417;
x_352 = x_419;
x_353 = x_437;
x_354 = x_421;
x_355 = x_422;
x_356 = lean_box(0);
goto block_408;
}
}
else
{
lean_object* x_438; 
lean_dec(x_432);
x_438 = lean_box(0);
x_340 = x_420;
x_341 = x_409;
x_342 = x_413;
x_343 = x_431;
x_344 = x_416;
x_345 = x_425;
x_346 = x_418;
x_347 = x_430;
x_348 = x_410;
x_349 = x_412;
x_350 = x_415;
x_351 = x_417;
x_352 = x_419;
x_353 = x_438;
x_354 = x_421;
x_355 = x_422;
x_356 = lean_box(0);
goto block_408;
}
}
}
block_467:
{
lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_455 = lean_unsigned_to_nat(6u);
x_456 = l_Lean_Syntax_getArg(x_1, x_455);
x_457 = l_Lean_Syntax_isNone(x_456);
if (x_457 == 0)
{
uint8_t x_458; 
lean_inc(x_456);
x_458 = l_Lean_Syntax_matchesNull(x_456, x_444);
if (x_458 == 0)
{
lean_object* x_459; 
lean_dec(x_456);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec(x_1);
x_459 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_459;
}
else
{
lean_object* x_460; lean_object* x_461; uint8_t x_462; 
x_460 = l_Lean_Syntax_getArg(x_456, x_51);
lean_dec(x_456);
x_461 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(x_460);
x_462 = l_Lean_Syntax_isOfKind(x_460, x_461);
if (x_462 == 0)
{
lean_object* x_463; 
lean_dec(x_460);
lean_dec(x_453);
lean_dec_ref(x_452);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec(x_1);
x_463 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_463;
}
else
{
lean_object* x_464; lean_object* x_465; 
x_464 = l_Lean_Syntax_getArg(x_460, x_450);
lean_dec(x_460);
x_465 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_465, 0, x_464);
x_409 = x_440;
x_410 = x_441;
x_411 = x_442;
x_412 = x_443;
x_413 = x_445;
x_414 = x_444;
x_415 = x_446;
x_416 = x_447;
x_417 = x_449;
x_418 = x_448;
x_419 = x_451;
x_420 = x_465;
x_421 = x_452;
x_422 = x_453;
x_423 = lean_box(0);
goto block_439;
}
}
}
else
{
lean_object* x_466; 
lean_dec(x_456);
x_466 = lean_box(0);
x_409 = x_440;
x_410 = x_441;
x_411 = x_442;
x_412 = x_443;
x_413 = x_445;
x_414 = x_444;
x_415 = x_446;
x_416 = x_447;
x_417 = x_449;
x_418 = x_448;
x_419 = x_451;
x_420 = x_466;
x_421 = x_452;
x_422 = x_453;
x_423 = lean_box(0);
goto block_439;
}
}
block_494:
{
lean_object* x_482; lean_object* x_483; uint8_t x_484; 
x_482 = lean_unsigned_to_nat(5u);
x_483 = l_Lean_Syntax_getArg(x_1, x_482);
x_484 = l_Lean_Syntax_isNone(x_483);
if (x_484 == 0)
{
uint8_t x_485; 
lean_inc(x_483);
x_485 = l_Lean_Syntax_matchesNull(x_483, x_472);
if (x_485 == 0)
{
lean_object* x_486; 
lean_dec(x_483);
lean_dec(x_480);
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_471);
lean_dec_ref(x_468);
lean_dec(x_1);
x_486 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; uint8_t x_489; 
x_487 = l_Lean_Syntax_getArg(x_483, x_51);
lean_dec(x_483);
x_488 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
lean_inc(x_487);
x_489 = l_Lean_Syntax_isOfKind(x_487, x_488);
if (x_489 == 0)
{
lean_object* x_490; 
lean_dec(x_487);
lean_dec(x_480);
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_471);
lean_dec_ref(x_468);
lean_dec(x_1);
x_490 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_490;
}
else
{
lean_object* x_491; lean_object* x_492; 
x_491 = l_Lean_Syntax_getArg(x_487, x_477);
lean_dec(x_487);
x_492 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_492, 0, x_491);
x_440 = x_478;
x_441 = x_468;
x_442 = x_469;
x_443 = x_470;
x_444 = x_472;
x_445 = x_471;
x_446 = x_473;
x_447 = x_474;
x_448 = x_476;
x_449 = x_475;
x_450 = x_477;
x_451 = x_492;
x_452 = x_479;
x_453 = x_480;
x_454 = lean_box(0);
goto block_467;
}
}
}
else
{
lean_object* x_493; 
lean_dec(x_483);
x_493 = lean_box(0);
x_440 = x_478;
x_441 = x_468;
x_442 = x_469;
x_443 = x_470;
x_444 = x_472;
x_445 = x_471;
x_446 = x_473;
x_447 = x_474;
x_448 = x_476;
x_449 = x_475;
x_450 = x_477;
x_451 = x_493;
x_452 = x_479;
x_453 = x_480;
x_454 = lean_box(0);
goto block_467;
}
}
block_521:
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_501 = lean_unsigned_to_nat(2u);
x_502 = l_Lean_Syntax_getArg(x_1, x_501);
x_503 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_504 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(x_502);
x_505 = l_Lean_Syntax_isOfKind(x_502, x_504);
if (x_505 == 0)
{
lean_object* x_506; 
lean_dec(x_502);
lean_dec(x_499);
lean_dec_ref(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_1);
x_506 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_506;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; uint8_t x_511; 
x_507 = lean_unsigned_to_nat(3u);
x_508 = l_Lean_Syntax_getArg(x_1, x_507);
x_509 = lean_unsigned_to_nat(4u);
x_510 = l_Lean_Syntax_getArg(x_1, x_509);
x_511 = l_Lean_Syntax_isNone(x_510);
if (x_511 == 0)
{
uint8_t x_512; 
lean_inc(x_510);
x_512 = l_Lean_Syntax_matchesNull(x_510, x_495);
if (x_512 == 0)
{
lean_object* x_513; 
lean_dec(x_510);
lean_dec(x_508);
lean_dec(x_502);
lean_dec(x_499);
lean_dec_ref(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_1);
x_513 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_513;
}
else
{
lean_object* x_514; lean_object* x_515; uint8_t x_516; 
x_514 = l_Lean_Syntax_getArg(x_510, x_51);
lean_dec(x_510);
x_515 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
lean_inc(x_514);
x_516 = l_Lean_Syntax_isOfKind(x_514, x_515);
if (x_516 == 0)
{
lean_object* x_517; 
lean_dec(x_514);
lean_dec(x_508);
lean_dec(x_502);
lean_dec(x_499);
lean_dec_ref(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_1);
x_517 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_517;
}
else
{
lean_object* x_518; lean_object* x_519; 
x_518 = l_Lean_Syntax_getArg(x_514, x_495);
lean_dec(x_514);
x_519 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_519, 0, x_518);
x_468 = x_503;
x_469 = x_501;
x_470 = x_509;
x_471 = x_502;
x_472 = x_495;
x_473 = x_508;
x_474 = x_497;
x_475 = x_504;
x_476 = x_496;
x_477 = x_507;
x_478 = x_519;
x_479 = x_498;
x_480 = x_499;
x_481 = lean_box(0);
goto block_494;
}
}
}
else
{
lean_object* x_520; 
lean_dec(x_510);
x_520 = lean_box(0);
x_468 = x_503;
x_469 = x_501;
x_470 = x_509;
x_471 = x_502;
x_472 = x_495;
x_473 = x_508;
x_474 = x_497;
x_475 = x_504;
x_476 = x_496;
x_477 = x_507;
x_478 = x_520;
x_479 = x_498;
x_480 = x_499;
x_481 = lean_box(0);
goto block_494;
}
}
}
block_539:
{
lean_object* x_526; lean_object* x_527; uint8_t x_528; 
x_526 = lean_unsigned_to_nat(1u);
x_527 = l_Lean_Syntax_getArg(x_1, x_526);
x_528 = l_Lean_Syntax_isNone(x_527);
if (x_528 == 0)
{
uint8_t x_529; 
lean_inc(x_527);
x_529 = l_Lean_Syntax_matchesNull(x_527, x_526);
if (x_529 == 0)
{
lean_object* x_530; 
lean_dec(x_527);
lean_dec(x_524);
lean_dec_ref(x_523);
lean_dec(x_522);
lean_dec(x_1);
x_530 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_530;
}
else
{
lean_object* x_531; lean_object* x_532; uint8_t x_533; 
x_531 = l_Lean_Syntax_getArg(x_527, x_51);
lean_dec(x_527);
x_532 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(x_531);
x_533 = l_Lean_Syntax_isOfKind(x_531, x_532);
if (x_533 == 0)
{
lean_object* x_534; 
lean_dec(x_531);
lean_dec(x_524);
lean_dec_ref(x_523);
lean_dec(x_522);
lean_dec(x_1);
x_534 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_534;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = l_Lean_Syntax_getArg(x_531, x_526);
lean_dec(x_531);
x_536 = l_Lean_Syntax_getArgs(x_535);
lean_dec(x_535);
x_537 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_537, 0, x_536);
x_495 = x_526;
x_496 = x_522;
x_497 = x_537;
x_498 = x_523;
x_499 = x_524;
x_500 = lean_box(0);
goto block_521;
}
}
}
else
{
lean_object* x_538; 
lean_dec(x_527);
x_538 = lean_box(0);
x_495 = x_526;
x_496 = x_522;
x_497 = x_538;
x_498 = x_523;
x_499 = x_524;
x_500 = lean_box(0);
goto block_521;
}
}
}
block_47:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_24 = l_Array_append___redArg(x_21, x_23);
lean_dec_ref(x_23);
lean_inc(x_14);
lean_inc(x_18);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_24);
x_26 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_16);
x_27 = l_Lean_Name_mkStr4(x_5, x_6, x_16, x_26);
x_28 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_16);
x_29 = l_Lean_Name_mkStr4(x_5, x_6, x_16, x_28);
x_30 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_18);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
x_33 = l_Lean_Name_mkStr4(x_5, x_6, x_16, x_32);
x_34 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
lean_inc(x_18);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_18);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_18);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_9);
lean_inc(x_18);
x_37 = l_Lean_Syntax_node3(x_18, x_33, x_35, x_10, x_36);
lean_inc(x_14);
lean_inc(x_18);
x_38 = l_Lean_Syntax_node1(x_18, x_14, x_37);
lean_inc(x_14);
lean_inc(x_18);
x_39 = l_Lean_Syntax_node1(x_18, x_14, x_38);
x_40 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_18);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_18);
x_42 = l_Lean_Syntax_node4(x_18, x_29, x_31, x_39, x_41, x_20);
lean_inc(x_18);
x_43 = l_Lean_Syntax_node1(x_18, x_14, x_42);
lean_inc(x_18);
x_44 = l_Lean_Syntax_node1(x_18, x_27, x_43);
lean_inc(x_22);
x_45 = l_Lean_Syntax_node8(x_18, x_15, x_19, x_22, x_12, x_11, x_22, x_8, x_25, x_44);
x_46 = l_Lean_Elab_Command_elabCommand(x_45, x_7, x_17);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabElab(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
x_4 = ((lean_object*)(l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Elab_MacroArgUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_MacroArgUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_AuxDef(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_MacroArgUtil(uint8_t builtin);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_MacroArgUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ElabRules(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ElabRules(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ElabRules(builtin);
}
#ifdef __cplusplus
}
#endif
