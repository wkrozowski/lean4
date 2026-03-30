// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.OrderInsts
// Imports: public import Lean.Meta.Tactic.Grind.SynthInstance
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Sym_sym_debug;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LawfulOrderLT"};
static const lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(125, 54, 67, 105, 183, 31, 31, 114)}};
static const lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "type has `LE` and `LT`, but the `LT` instance is not lawful, failed to synthesize"};
static const lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "IsPreorder"};
static const lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 213, 76, 156, 147, 68, 250, 139)}};
static const lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "type has `LE`, but is not a preorder, failed to synthesize"};
static const lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "IsPartialOrder"};
static const lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 84, 36, 174, 137, 182, 135, 55)}};
static const lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "type has `LE`, but is not a partial order, failed to synthesize"};
static const lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "IsLinearOrder"};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "type has `LE`, but is not a linear order, failed to synthesize"};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "IsLinearPreorder"};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 98, 195, 196, 59, 47, 77, 198)}};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "type has `LE`, but is not a linear preorder, failed to synthesize"};
static const lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref(v_val_8_);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = ((lean_object*)(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3));
v___x_22_ = l_Lean_stringToMessageData(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object* v_u_23_, lean_object* v_type_24_, lean_object* v_ltInst_x3f_25_, lean_object* v_leInst_x3f_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
if (lean_obj_tag(v_ltInst_x3f_25_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_26_) == 1)
{
lean_object* v_val_37_; lean_object* v_val_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v_lawfulOrderLTType_43_; lean_object* v___x_44_; 
v_val_37_ = lean_ctor_get(v_ltInst_x3f_25_, 0);
lean_inc(v_val_37_);
lean_dec_ref(v_ltInst_x3f_25_);
v_val_38_ = lean_ctor_get(v_leInst_x3f_26_, 0);
lean_inc(v_val_38_);
lean_dec_ref(v_leInst_x3f_26_);
v___x_39_ = ((lean_object*)(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2));
v___x_40_ = lean_box(0);
v___x_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_41_, 0, v_u_23_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
v___x_42_ = l_Lean_mkConst(v___x_39_, v___x_41_);
v_lawfulOrderLTType_43_ = l_Lean_mkApp3(v___x_42_, v_type_24_, v_val_37_, v_val_38_);
lean_inc_ref(v_lawfulOrderLTType_43_);
v___x_44_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_lawfulOrderLTType_43_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_a_45_);
if (lean_obj_tag(v_a_45_) == 1)
{
lean_dec_ref(v_a_45_);
lean_dec_ref(v_lawfulOrderLTType_43_);
return v___x_44_;
}
else
{
lean_object* v___x_46_; 
lean_dec(v_a_45_);
lean_dec_ref(v___x_44_);
v___x_46_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_27_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; uint8_t v___x_48_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
lean_dec_ref(v___x_46_);
v___x_48_ = lean_unbox(v_a_47_);
lean_dec(v_a_47_);
if (v___x_48_ == 0)
{
lean_dec_ref(v_lawfulOrderLTType_43_);
goto v___jp_34_;
}
else
{
lean_object* v_options_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_options_49_ = lean_ctor_get(v_a_31_, 2);
v___x_50_ = l_Lean_Meta_Sym_sym_debug;
v___x_51_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_49_, v___x_50_);
if (v___x_51_ == 0)
{
lean_dec_ref(v_lawfulOrderLTType_43_);
goto v___jp_34_;
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_obj_once(&l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4, &l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4);
v___x_53_ = l_Lean_indentExpr(v_lawfulOrderLTType_43_);
v___x_54_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = l_Lean_Meta_Sym_reportIssue(v___x_54_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_dec_ref(v___x_55_);
goto v___jp_34_;
}
else
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
v_a_56_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v___x_55_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_55_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
}
else
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
lean_dec_ref(v_lawfulOrderLTType_43_);
v_a_64_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v___x_46_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_46_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_a_64_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
else
{
lean_dec_ref(v_lawfulOrderLTType_43_);
return v___x_44_;
}
}
else
{
lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_79_; 
lean_dec(v_leInst_x3f_26_);
lean_dec_ref(v_type_24_);
lean_dec(v_u_23_);
v_isSharedCheck_79_ = !lean_is_exclusive(v_ltInst_x3f_25_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v_ltInst_x3f_25_, 0);
lean_dec(v_unused_80_);
v___x_73_ = v_ltInst_x3f_25_;
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
else
{
lean_dec(v_ltInst_x3f_25_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_75_ = lean_box(0);
if (v_isShared_74_ == 0)
{
lean_ctor_set_tag(v___x_73_, 0);
lean_ctor_set(v___x_73_, 0, v___x_75_);
v___x_77_ = v___x_73_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_leInst_x3f_26_);
lean_dec(v_ltInst_x3f_25_);
lean_dec_ref(v_type_24_);
lean_dec(v_u_23_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
v___jp_34_:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_box(0);
v___x_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___boxed(lean_object* v_u_83_, lean_object* v_type_84_, lean_object* v_ltInst_x3f_85_, lean_object* v_leInst_x3f_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_u_83_, v_type_84_, v_ltInst_x3f_85_, v_leInst_x3f_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(lean_object* v_u_95_, lean_object* v_type_96_, lean_object* v_ltInst_x3f_97_, lean_object* v_leInst_x3f_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_u_95_, v_type_96_, v_ltInst_x3f_97_, v_leInst_x3f_98_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___boxed(lean_object* v_u_111_, lean_object* v_type_112_, lean_object* v_ltInst_x3f_113_, lean_object* v_leInst_x3f_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(v_u_111_, v_type_112_, v_ltInst_x3f_113_, v_leInst_x3f_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec(v_a_115_);
return v_res_126_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2));
v___x_133_ = l_Lean_stringToMessageData(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object* v_u_134_, lean_object* v_type_135_, lean_object* v_leInst_x3f_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_136_) == 1)
{
lean_object* v_val_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_isPreorderType_152_; lean_object* v___x_153_; 
v_val_147_ = lean_ctor_get(v_leInst_x3f_136_, 0);
lean_inc(v_val_147_);
lean_dec_ref(v_leInst_x3f_136_);
v___x_148_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1));
v___x_149_ = lean_box(0);
v___x_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_150_, 0, v_u_134_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = l_Lean_mkConst(v___x_148_, v___x_150_);
v_isPreorderType_152_ = l_Lean_mkAppB(v___x_151_, v_type_135_, v_val_147_);
lean_inc_ref(v_isPreorderType_152_);
v___x_153_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_isPreorderType_152_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
if (lean_obj_tag(v_a_154_) == 1)
{
lean_dec_ref(v_a_154_);
lean_dec_ref(v_isPreorderType_152_);
return v___x_153_;
}
else
{
lean_object* v___x_155_; 
lean_dec(v_a_154_);
lean_dec_ref(v___x_153_);
v___x_155_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_137_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; uint8_t v___x_157_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref(v___x_155_);
v___x_157_ = lean_unbox(v_a_156_);
lean_dec(v_a_156_);
if (v___x_157_ == 0)
{
lean_dec_ref(v_isPreorderType_152_);
goto v___jp_144_;
}
else
{
lean_object* v_options_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_options_158_ = lean_ctor_get(v_a_141_, 2);
v___x_159_ = l_Lean_Meta_Sym_sym_debug;
v___x_160_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec_ref(v_isPreorderType_152_);
goto v___jp_144_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3);
v___x_162_ = l_Lean_indentExpr(v_isPreorderType_152_);
v___x_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = l_Lean_Meta_Sym_reportIssue(v___x_163_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_dec_ref(v___x_164_);
goto v___jp_144_;
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec_ref(v_isPreorderType_152_);
v_a_173_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_155_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_155_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
else
{
lean_dec_ref(v_isPreorderType_152_);
return v___x_153_;
}
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_leInst_x3f_136_);
lean_dec_ref(v_type_135_);
lean_dec(v_u_134_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
v___jp_144_:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_box(0);
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___boxed(lean_object* v_u_183_, lean_object* v_type_184_, lean_object* v_leInst_x3f_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_u_183_, v_type_184_, v_leInst_x3f_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f(lean_object* v_u_194_, lean_object* v_type_195_, lean_object* v_leInst_x3f_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_u_194_, v_type_195_, v_leInst_x3f_196_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___boxed(lean_object* v_u_209_, lean_object* v_type_210_, lean_object* v_leInst_x3f_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f(v_u_209_, v_type_210_, v_leInst_x3f_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec(v_a_212_);
return v_res_223_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2));
v___x_230_ = l_Lean_stringToMessageData(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object* v_u_231_, lean_object* v_type_232_, lean_object* v_leInst_x3f_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_233_) == 1)
{
lean_object* v_val_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_isPartialOrderType_249_; lean_object* v___x_250_; 
v_val_244_ = lean_ctor_get(v_leInst_x3f_233_, 0);
lean_inc(v_val_244_);
lean_dec_ref(v_leInst_x3f_233_);
v___x_245_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1));
v___x_246_ = lean_box(0);
v___x_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_247_, 0, v_u_231_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = l_Lean_mkConst(v___x_245_, v___x_247_);
v_isPartialOrderType_249_ = l_Lean_mkAppB(v___x_248_, v_type_232_, v_val_244_);
lean_inc_ref(v_isPartialOrderType_249_);
v___x_250_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_isPartialOrderType_249_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
if (lean_obj_tag(v_a_251_) == 1)
{
lean_dec_ref(v_a_251_);
lean_dec_ref(v_isPartialOrderType_249_);
return v___x_250_;
}
else
{
lean_object* v___x_252_; 
lean_dec_ref(v___x_250_);
lean_dec(v_a_251_);
v___x_252_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_234_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; uint8_t v___x_254_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref(v___x_252_);
v___x_254_ = lean_unbox(v_a_253_);
lean_dec(v_a_253_);
if (v___x_254_ == 0)
{
lean_dec_ref(v_isPartialOrderType_249_);
goto v___jp_241_;
}
else
{
lean_object* v_options_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_options_255_ = lean_ctor_get(v_a_238_, 2);
v___x_256_ = l_Lean_Meta_Sym_sym_debug;
v___x_257_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_dec_ref(v_isPartialOrderType_249_);
goto v___jp_241_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_258_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3);
v___x_259_ = l_Lean_indentExpr(v_isPartialOrderType_249_);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = l_Lean_Meta_Sym_reportIssue(v___x_260_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_dec_ref(v___x_261_);
goto v___jp_241_;
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v_isPartialOrderType_249_);
v_a_270_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_252_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_252_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
else
{
lean_dec_ref(v_isPartialOrderType_249_);
return v___x_250_;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_leInst_x3f_233_);
lean_dec_ref(v_type_232_);
lean_dec(v_u_231_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
v___jp_241_:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_box(0);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___boxed(lean_object* v_u_280_, lean_object* v_type_281_, lean_object* v_leInst_x3f_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_u_280_, v_type_281_, v_leInst_x3f_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(lean_object* v_u_291_, lean_object* v_type_292_, lean_object* v_leInst_x3f_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_u_291_, v_type_292_, v_leInst_x3f_293_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___boxed(lean_object* v_u_306_, lean_object* v_type_307_, lean_object* v_leInst_x3f_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(v_u_306_, v_type_307_, v_leInst_x3f_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec(v_a_309_);
return v_res_320_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2));
v___x_327_ = l_Lean_stringToMessageData(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(lean_object* v_u_328_, lean_object* v_type_329_, lean_object* v_leInst_x3f_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_330_) == 1)
{
lean_object* v_val_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_isLinearOrderType_346_; lean_object* v___x_347_; 
v_val_341_ = lean_ctor_get(v_leInst_x3f_330_, 0);
lean_inc(v_val_341_);
lean_dec_ref(v_leInst_x3f_330_);
v___x_342_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1));
v___x_343_ = lean_box(0);
v___x_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_344_, 0, v_u_328_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_mkConst(v___x_342_, v___x_344_);
v_isLinearOrderType_346_ = l_Lean_mkAppB(v___x_345_, v_type_329_, v_val_341_);
lean_inc_ref(v_isLinearOrderType_346_);
v___x_347_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_isLinearOrderType_346_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
if (lean_obj_tag(v_a_348_) == 1)
{
lean_dec_ref(v_a_348_);
lean_dec_ref(v_isLinearOrderType_346_);
return v___x_347_;
}
else
{
lean_object* v___x_349_; 
lean_dec(v_a_348_);
lean_dec_ref(v___x_347_);
v___x_349_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_331_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; uint8_t v___x_351_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref(v___x_349_);
v___x_351_ = lean_unbox(v_a_350_);
lean_dec(v_a_350_);
if (v___x_351_ == 0)
{
lean_dec_ref(v_isLinearOrderType_346_);
goto v___jp_338_;
}
else
{
lean_object* v_options_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_options_352_ = lean_ctor_get(v_a_335_, 2);
v___x_353_ = l_Lean_Meta_Sym_sym_debug;
v___x_354_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_dec_ref(v_isLinearOrderType_346_);
goto v___jp_338_;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3);
v___x_356_ = l_Lean_indentExpr(v_isLinearOrderType_346_);
v___x_357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = l_Lean_Meta_Sym_reportIssue(v___x_357_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_dec_ref(v___x_358_);
goto v___jp_338_;
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec_ref(v_isLinearOrderType_346_);
v_a_367_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_349_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_349_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
else
{
lean_dec_ref(v_isLinearOrderType_346_);
return v___x_347_;
}
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec(v_leInst_x3f_330_);
lean_dec_ref(v_type_329_);
lean_dec(v_u_328_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
v___jp_338_:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_box(0);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___boxed(lean_object* v_u_377_, lean_object* v_type_378_, lean_object* v_leInst_x3f_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_u_377_, v_type_378_, v_leInst_x3f_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(lean_object* v_u_388_, lean_object* v_type_389_, lean_object* v_leInst_x3f_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_u_388_, v_type_389_, v_leInst_x3f_390_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___boxed(lean_object* v_u_403_, lean_object* v_type_404_, lean_object* v_leInst_x3f_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(v_u_403_, v_type_404_, v_leInst_x3f_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec(v_a_406_);
return v_res_417_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2));
v___x_424_ = l_Lean_stringToMessageData(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(lean_object* v_u_425_, lean_object* v_type_426_, lean_object* v_leInst_x3f_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_427_) == 1)
{
lean_object* v_val_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_isLinearOrderType_443_; lean_object* v___x_444_; 
v_val_438_ = lean_ctor_get(v_leInst_x3f_427_, 0);
lean_inc(v_val_438_);
lean_dec_ref(v_leInst_x3f_427_);
v___x_439_ = ((lean_object*)(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1));
v___x_440_ = lean_box(0);
v___x_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_441_, 0, v_u_425_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = l_Lean_mkConst(v___x_439_, v___x_441_);
v_isLinearOrderType_443_ = l_Lean_mkAppB(v___x_442_, v_type_426_, v_val_438_);
lean_inc_ref(v_isLinearOrderType_443_);
v___x_444_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_isLinearOrderType_443_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
if (lean_obj_tag(v_a_445_) == 1)
{
lean_dec_ref(v_a_445_);
lean_dec_ref(v_isLinearOrderType_443_);
return v___x_444_;
}
else
{
lean_object* v___x_446_; 
lean_dec(v_a_445_);
lean_dec_ref(v___x_444_);
v___x_446_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_428_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; uint8_t v___x_448_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref(v___x_446_);
v___x_448_ = lean_unbox(v_a_447_);
lean_dec(v_a_447_);
if (v___x_448_ == 0)
{
lean_dec_ref(v_isLinearOrderType_443_);
goto v___jp_435_;
}
else
{
lean_object* v_options_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_options_449_ = lean_ctor_get(v_a_432_, 2);
v___x_450_ = l_Lean_Meta_Sym_sym_debug;
v___x_451_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_dec_ref(v_isLinearOrderType_443_);
goto v___jp_435_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_452_ = lean_obj_once(&l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3, &l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3);
v___x_453_ = l_Lean_indentExpr(v_isLinearOrderType_443_);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_Meta_Sym_reportIssue(v___x_454_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_dec_ref(v___x_455_);
goto v___jp_435_;
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec_ref(v_isLinearOrderType_443_);
v_a_464_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_446_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_446_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
else
{
lean_dec_ref(v_isLinearOrderType_443_);
return v___x_444_;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec(v_leInst_x3f_427_);
lean_dec_ref(v_type_426_);
lean_dec(v_u_425_);
v___x_472_ = lean_box(0);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
v___jp_435_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_box(0);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___boxed(lean_object* v_u_474_, lean_object* v_type_475_, lean_object* v_leInst_x3f_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(v_u_474_, v_type_475_, v_leInst_x3f_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(lean_object* v_u_485_, lean_object* v_type_486_, lean_object* v_leInst_x3f_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(v_u_485_, v_type_486_, v_leInst_x3f_487_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___boxed(lean_object* v_u_500_, lean_object* v_type_501_, lean_object* v_leInst_x3f_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(v_u_500_, v_type_501_, v_leInst_x3f_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec(v_a_503_);
return v_res_514_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
}
#ifdef __cplusplus
}
#endif
