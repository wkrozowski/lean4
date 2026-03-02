// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CtorIdx
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Constructions.CtorIdx import Lean.Meta.CtorIdxHInj
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
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.Tactic.Grind.CtorIdx"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Grind.propagateCtorIdxUp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 162, .m_capacity = 162, .m_length = 161, .m_data = "assertion violation: aType.isAppOfArity indInfo.name (indInfo.numParams + indInfo.numIndices)\n      -- both types should be headed by the same type former\n      "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* l_Lean_executeReservedNameAction(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0);
x_14 = lean_panic_fn(x_13, x_1);
x_15 = lean_apply_11(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_15;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3));
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(37u);
x_4 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2));
x_5 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_2);
x_18 = lean_array_set(x_3, x_4, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_4, x_19);
lean_dec(x_4);
x_2 = x_16;
x_3 = x_18;
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = l_Lean_Expr_constName_x3f(x_2);
lean_dec_ref(x_2);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_316; 
x_23 = lean_ctor_get(x_22, 0);
x_316 = !lean_is_exclusive(x_22);
if (x_316 == 0)
{
x_24 = x_22;
x_25 = x_316;
goto block_315;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_316;
goto block_315;
}
block_315:
{
lean_object* x_26; 
x_26 = l_isCtorIdx_x3f___redArg(x_23, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_306; 
x_27 = lean_ctor_get(x_26, 0);
x_306 = !lean_is_exclusive(x_26);
if (x_306 == 0)
{
x_28 = x_26;
x_29 = x_306;
goto block_305;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_306;
goto block_305;
}
block_305:
{
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_300; 
x_30 = lean_ctor_get(x_27, 0);
x_300 = !lean_is_exclusive(x_27);
if (x_300 == 0)
{
x_31 = x_27;
x_32 = x_300;
goto block_299;
}
else
{
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = x_300;
goto block_299;
}
block_299:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 2);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_array_get_size(x_3);
x_37 = lean_nat_add(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_37, x_38);
x_40 = lean_nat_dec_eq(x_36, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_41 = lean_box(0);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_41);
x_42 = x_28;
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
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_del_object(x_28);
x_45 = l_Lean_instInhabitedExpr;
x_46 = l_Array_back_x21___redArg(x_45, x_3);
lean_dec_ref(x_3);
lean_inc(x_46);
x_47 = l_Lean_Meta_Grind_getRootENode___redArg(x_46, x_5, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_290; 
x_48 = lean_ctor_get(x_47, 0);
x_290 = !lean_is_exclusive(x_47);
if (x_290 == 0)
{
x_49 = x_47;
x_50 = x_290;
goto block_289;
}
else
{
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = x_290;
goto block_289;
}
block_289:
{
lean_object* x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get_uint8(x_48, sizeof(void*)*11 + 2);
x_53 = lean_ctor_get_uint8(x_48, sizeof(void*)*11 + 4);
lean_dec(x_48);
if (x_52 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_111 = lean_box(0);
if (x_50 == 0)
{
lean_ctor_set(x_49, 0, x_111);
x_112 = x_49;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_111);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
else
{
lean_object* x_115; 
lean_del_object(x_49);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_51);
x_115 = l_Lean_Meta_isConstructorApp_x3f(x_51, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_280; 
x_116 = lean_ctor_get(x_115, 0);
x_280 = !lean_is_exclusive(x_115);
if (x_280 == 0)
{
x_117 = x_115;
x_118 = x_280;
goto block_279;
}
else
{
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_box(0);
x_118 = x_280;
goto block_279;
}
block_279:
{
if (lean_obj_tag(x_116) == 1)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_del_object(x_117);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec_ref(x_116);
if (x_53 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
x_120 = x_5;
x_121 = x_6;
x_122 = x_7;
x_123 = x_8;
x_124 = x_9;
x_125 = x_10;
x_126 = x_11;
x_127 = x_12;
x_128 = x_13;
x_129 = x_14;
x_130 = lean_box(0);
goto block_180;
}
else
{
lean_object* x_181; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_51);
lean_inc(x_46);
x_181 = l_Lean_Meta_Grind_hasSameType(x_46, x_51, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; uint8_t x_183; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec_ref(x_181);
x_183 = lean_unbox(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec(x_119);
lean_dec_ref(x_1);
x_184 = l_Lean_Meta_Grind_getGeneration___redArg(x_46, x_5);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = l_Lean_Meta_Grind_getGeneration___redArg(x_51, x_5);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_250; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec_ref(x_186);
x_250 = lean_nat_dec_le(x_185, x_187);
if (x_250 == 0)
{
lean_dec(x_187);
x_188 = x_185;
goto block_249;
}
else
{
lean_dec(x_185);
x_188 = x_187;
goto block_249;
}
block_249:
{
lean_object* x_189; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_46);
x_189 = lean_infer_type(x_46, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec_ref(x_189);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_191 = l_Lean_Meta_whnfD(x_190, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_51);
x_193 = lean_infer_type(x_51, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_195 = l_Lean_Meta_whnfD(x_194, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_216; 
x_196 = lean_ctor_get(x_195, 0);
x_216 = !lean_is_exclusive(x_195);
if (x_216 == 0)
{
x_197 = x_195;
x_198 = x_216;
goto block_215;
}
else
{
lean_inc(x_196);
lean_dec(x_195);
x_197 = lean_box(0);
x_198 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_33, 0);
lean_inc(x_199);
lean_dec_ref(x_33);
lean_inc(x_37);
x_200 = l_Lean_Expr_isAppOfArity(x_192, x_199, x_37);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_199);
lean_del_object(x_197);
lean_dec(x_196);
lean_dec(x_192);
lean_dec(x_188);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec(x_37);
lean_del_object(x_31);
lean_del_object(x_24);
x_201 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
x_202 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_201, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_202;
}
else
{
uint8_t x_203; 
x_203 = l_Lean_Expr_isAppOfArity(x_196, x_199, x_37);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_199);
lean_dec(x_196);
lean_dec(x_192);
lean_dec(x_188);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_204 = lean_box(0);
if (x_198 == 0)
{
lean_ctor_set(x_197, 0, x_204);
x_205 = x_197;
goto block_206;
}
else
{
lean_object* x_207; 
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_204);
x_205 = x_207;
goto block_206;
}
block_206:
{
return x_205;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_del_object(x_197);
x_208 = lean_st_ref_get(x_14);
x_209 = lean_ctor_get(x_208, 0);
lean_inc_ref(x_209);
lean_dec(x_208);
x_210 = l_Lean_Expr_getAppFn(x_192);
x_211 = l_Lean_Expr_constLevels_x21(x_210);
lean_dec_ref(x_210);
x_212 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_199);
x_213 = l_Lean_Environment_containsOnBranch(x_209, x_212);
if (x_213 == 0)
{
lean_object* x_214; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_212);
x_214 = l_Lean_executeReservedNameAction(x_212, x_13, x_14);
if (lean_obj_tag(x_214) == 0)
{
lean_dec_ref(x_214);
x_54 = x_192;
x_55 = x_211;
x_56 = x_196;
x_57 = x_188;
x_58 = x_212;
x_59 = x_5;
x_60 = x_6;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = x_11;
x_66 = x_12;
x_67 = x_13;
x_68 = x_14;
x_69 = lean_box(0);
goto block_110;
}
else
{
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_196);
lean_dec(x_192);
lean_dec(x_188);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_214;
}
}
else
{
x_54 = x_192;
x_55 = x_211;
x_56 = x_196;
x_57 = x_188;
x_58 = x_212;
x_59 = x_5;
x_60 = x_6;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = x_11;
x_66 = x_12;
x_67 = x_13;
x_68 = x_14;
x_69 = lean_box(0);
goto block_110;
}
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; uint8_t x_224; 
lean_dec(x_192);
lean_dec(x_188);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_217 = lean_ctor_get(x_195, 0);
x_224 = !lean_is_exclusive(x_195);
if (x_224 == 0)
{
x_218 = x_195;
x_219 = x_224;
goto block_223;
}
else
{
lean_inc(x_217);
lean_dec(x_195);
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
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_232; 
lean_dec(x_192);
lean_dec(x_188);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_225 = lean_ctor_get(x_193, 0);
x_232 = !lean_is_exclusive(x_193);
if (x_232 == 0)
{
x_226 = x_193;
x_227 = x_232;
goto block_231;
}
else
{
lean_inc(x_225);
lean_dec(x_193);
x_226 = lean_box(0);
x_227 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_228; 
if (x_227 == 0)
{
x_228 = x_226;
goto block_229;
}
else
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_225);
x_228 = x_230;
goto block_229;
}
block_229:
{
return x_228;
}
}
}
}
else
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; uint8_t x_240; 
lean_dec(x_188);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_233 = lean_ctor_get(x_191, 0);
x_240 = !lean_is_exclusive(x_191);
if (x_240 == 0)
{
x_234 = x_191;
x_235 = x_240;
goto block_239;
}
else
{
lean_inc(x_233);
lean_dec(x_191);
x_234 = lean_box(0);
x_235 = x_240;
goto block_239;
}
block_239:
{
lean_object* x_236; 
if (x_235 == 0)
{
x_236 = x_234;
goto block_237;
}
else
{
lean_object* x_238; 
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_233);
x_236 = x_238;
goto block_237;
}
block_237:
{
return x_236;
}
}
}
}
else
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_248; 
lean_dec(x_188);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_241 = lean_ctor_get(x_189, 0);
x_248 = !lean_is_exclusive(x_189);
if (x_248 == 0)
{
x_242 = x_189;
x_243 = x_248;
goto block_247;
}
else
{
lean_inc(x_241);
lean_dec(x_189);
x_242 = lean_box(0);
x_243 = x_248;
goto block_247;
}
block_247:
{
lean_object* x_244; 
if (x_243 == 0)
{
x_244 = x_242;
goto block_245;
}
else
{
lean_object* x_246; 
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_241);
x_244 = x_246;
goto block_245;
}
block_245:
{
return x_244;
}
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_258; 
lean_dec(x_185);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_251 = lean_ctor_get(x_186, 0);
x_258 = !lean_is_exclusive(x_186);
if (x_258 == 0)
{
x_252 = x_186;
x_253 = x_258;
goto block_257;
}
else
{
lean_inc(x_251);
lean_dec(x_186);
x_252 = lean_box(0);
x_253 = x_258;
goto block_257;
}
block_257:
{
lean_object* x_254; 
if (x_253 == 0)
{
x_254 = x_252;
goto block_255;
}
else
{
lean_object* x_256; 
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_251);
x_254 = x_256;
goto block_255;
}
block_255:
{
return x_254;
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_266; 
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_259 = lean_ctor_get(x_184, 0);
x_266 = !lean_is_exclusive(x_184);
if (x_266 == 0)
{
x_260 = x_184;
x_261 = x_266;
goto block_265;
}
else
{
lean_inc(x_259);
lean_dec(x_184);
x_260 = lean_box(0);
x_261 = x_266;
goto block_265;
}
block_265:
{
lean_object* x_262; 
if (x_261 == 0)
{
x_262 = x_260;
goto block_263;
}
else
{
lean_object* x_264; 
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_259);
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
else
{
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
x_120 = x_5;
x_121 = x_6;
x_122 = x_7;
x_123 = x_8;
x_124 = x_9;
x_125 = x_10;
x_126 = x_11;
x_127 = x_12;
x_128 = x_13;
x_129 = x_14;
x_130 = lean_box(0);
goto block_180;
}
}
else
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_274; 
lean_dec(x_119);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_267 = lean_ctor_get(x_181, 0);
x_274 = !lean_is_exclusive(x_181);
if (x_274 == 0)
{
x_268 = x_181;
x_269 = x_274;
goto block_273;
}
else
{
lean_inc(x_267);
lean_dec(x_181);
x_268 = lean_box(0);
x_269 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_270; 
if (x_269 == 0)
{
x_270 = x_268;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_267);
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
block_180:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_119, 2);
lean_inc(x_131);
lean_dec(x_119);
x_132 = l_Lean_mkNatLit(x_131);
x_133 = l_Lean_Meta_Sym_shareCommon___redArg(x_132, x_125);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_unsigned_to_nat(0u);
x_136 = lean_box(0);
lean_inc(x_129);
lean_inc_ref(x_128);
lean_inc(x_127);
lean_inc_ref(x_126);
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc(x_123);
lean_inc_ref(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_134);
x_137 = lean_grind_internalize(x_134, x_135, x_136, x_120, x_121, x_122, x_123, x_124, x_125, x_126, x_127, x_128, x_129);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
lean_dec_ref(x_137);
lean_inc(x_129);
lean_inc_ref(x_128);
lean_inc(x_127);
lean_inc_ref(x_126);
lean_inc_ref(x_122);
lean_inc(x_120);
x_138 = lean_grind_mk_eq_proof(x_46, x_51, x_120, x_121, x_122, x_123, x_124, x_125, x_126, x_127, x_128, x_129);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
x_140 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_129);
lean_inc_ref(x_128);
lean_inc(x_127);
lean_inc_ref(x_126);
x_141 = l_Lean_Meta_mkCongrArg(x_140, x_139, x_126, x_127, x_128, x_129);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
lean_inc(x_129);
lean_inc_ref(x_128);
lean_inc(x_127);
lean_inc_ref(x_126);
lean_inc(x_134);
lean_inc_ref(x_1);
x_143 = l_Lean_Meta_mkEq(x_1, x_134, x_126, x_127, x_128, x_129);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_145 = l_Lean_Meta_mkExpectedPropHint(x_142, x_144);
x_146 = 0;
x_147 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_134, x_145, x_146, x_120, x_122, x_126, x_127, x_128, x_129);
lean_dec_ref(x_122);
lean_dec(x_120);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_155; 
lean_dec(x_142);
lean_dec(x_134);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_122);
lean_dec(x_120);
lean_dec_ref(x_1);
x_148 = lean_ctor_get(x_143, 0);
x_155 = !lean_is_exclusive(x_143);
if (x_155 == 0)
{
x_149 = x_143;
x_150 = x_155;
goto block_154;
}
else
{
lean_inc(x_148);
lean_dec(x_143);
x_149 = lean_box(0);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_150 == 0)
{
x_151 = x_149;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_148);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_163; 
lean_dec(x_134);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_122);
lean_dec(x_120);
lean_dec_ref(x_1);
x_156 = lean_ctor_get(x_141, 0);
x_163 = !lean_is_exclusive(x_141);
if (x_163 == 0)
{
x_157 = x_141;
x_158 = x_163;
goto block_162;
}
else
{
lean_inc(x_156);
lean_dec(x_141);
x_157 = lean_box(0);
x_158 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_159; 
if (x_158 == 0)
{
x_159 = x_157;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_156);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_171; 
lean_dec(x_134);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_122);
lean_dec(x_120);
lean_dec_ref(x_1);
x_164 = lean_ctor_get(x_138, 0);
x_171 = !lean_is_exclusive(x_138);
if (x_171 == 0)
{
x_165 = x_138;
x_166 = x_171;
goto block_170;
}
else
{
lean_inc(x_164);
lean_dec(x_138);
x_165 = lean_box(0);
x_166 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_167; 
if (x_166 == 0)
{
x_167 = x_165;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_164);
x_167 = x_169;
goto block_168;
}
block_168:
{
return x_167;
}
}
}
}
else
{
lean_dec(x_134);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec_ref(x_1);
return x_137;
}
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_179; 
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec_ref(x_1);
x_172 = lean_ctor_get(x_133, 0);
x_179 = !lean_is_exclusive(x_133);
if (x_179 == 0)
{
x_173 = x_133;
x_174 = x_179;
goto block_178;
}
else
{
lean_inc(x_172);
lean_dec(x_133);
x_173 = lean_box(0);
x_174 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_175; 
if (x_174 == 0)
{
x_175 = x_173;
goto block_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_172);
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
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_116);
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_275 = lean_box(0);
if (x_118 == 0)
{
lean_ctor_set(x_117, 0, x_275);
x_276 = x_117;
goto block_277;
}
else
{
lean_object* x_278; 
x_278 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_278, 0, x_275);
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
lean_dec_ref(x_51);
lean_dec(x_46);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_281 = lean_ctor_get(x_115, 0);
x_288 = !lean_is_exclusive(x_115);
if (x_288 == 0)
{
x_282 = x_115;
x_283 = x_288;
goto block_287;
}
else
{
lean_inc(x_281);
lean_dec(x_115);
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
block_110:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_inc(x_58);
x_70 = l_Lean_mkConst(x_58, x_55);
x_71 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
x_72 = l_Lean_Expr_getAppNumArgs(x_54);
lean_inc(x_72);
x_73 = lean_mk_array(x_72, x_71);
x_74 = lean_nat_sub(x_72, x_38);
lean_dec(x_72);
x_75 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_54, x_73, x_74);
x_76 = l_Lean_mkAppN(x_70, x_75);
lean_dec_ref(x_75);
x_77 = l_Lean_Expr_app___override(x_76, x_46);
x_78 = l_Lean_Expr_getAppNumArgs(x_56);
lean_inc(x_78);
x_79 = lean_mk_array(x_78, x_71);
x_80 = lean_nat_sub(x_78, x_38);
lean_dec(x_78);
x_81 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_56, x_79, x_80);
x_82 = l_Lean_mkAppN(x_77, x_81);
lean_dec_ref(x_81);
x_83 = l_Lean_Expr_app___override(x_82, x_51);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc_ref(x_83);
x_84 = lean_infer_type(x_83, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
if (x_32 == 0)
{
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_58);
x_86 = x_31;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_58);
x_86 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_87; 
if (x_25 == 0)
{
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 0, x_86);
x_87 = x_24;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(x_99, 0, x_86);
x_87 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_88; 
x_88 = l_Lean_Meta_Grind_addNewRawFact(x_83, x_85, x_57, x_87, x_59, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec(x_59);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; uint8_t x_96; 
x_96 = !lean_is_exclusive(x_88);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_88, 0);
lean_dec(x_97);
x_89 = x_88;
x_90 = x_96;
goto block_95;
}
else
{
lean_dec(x_88);
x_89 = lean_box(0);
x_90 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_box(0);
if (x_90 == 0)
{
lean_ctor_set(x_89, 0, x_91);
x_92 = x_89;
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
return x_88;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_109; 
lean_dec_ref(x_83);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_del_object(x_31);
lean_del_object(x_24);
x_102 = lean_ctor_get(x_84, 0);
x_109 = !lean_is_exclusive(x_84);
if (x_109 == 0)
{
x_103 = x_84;
x_104 = x_109;
goto block_108;
}
else
{
lean_inc(x_102);
lean_dec(x_84);
x_103 = lean_box(0);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_104 == 0)
{
x_105 = x_103;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_102);
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
}
}
else
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; uint8_t x_298; 
lean_dec(x_46);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_291 = lean_ctor_get(x_47, 0);
x_298 = !lean_is_exclusive(x_47);
if (x_298 == 0)
{
x_292 = x_47;
x_293 = x_298;
goto block_297;
}
else
{
lean_inc(x_291);
lean_dec(x_47);
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
else
{
lean_object* x_301; lean_object* x_302; 
lean_dec(x_27);
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_301 = lean_box(0);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_301);
x_302 = x_28;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_304, 0, x_301);
x_302 = x_304;
goto block_303;
}
block_303:
{
return x_302;
}
}
}
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; uint8_t x_314; 
lean_del_object(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_307 = lean_ctor_get(x_26, 0);
x_314 = !lean_is_exclusive(x_26);
if (x_314 == 0)
{
x_308 = x_26;
x_309 = x_314;
goto block_313;
}
else
{
lean_inc(x_307);
lean_dec(x_26);
x_308 = lean_box(0);
x_309 = x_314;
goto block_313;
}
block_313:
{
lean_object* x_310; 
if (x_309 == 0)
{
x_310 = x_308;
goto block_311;
}
else
{
lean_object* x_312; 
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_307);
x_310 = x_312;
goto block_311;
}
block_311:
{
return x_310;
}
}
}
}
}
else
{
lean_object* x_317; lean_object* x_318; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_317 = lean_box(0);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_317);
return x_318;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
x_14 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_14);
x_15 = lean_mk_array(x_14, x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_14, x_16);
lean_dec(x_14);
lean_inc_ref(x_1);
x_18 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(x_1, x_1, x_15, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateCtorIdxUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorIdxHInj(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorIdxHInj(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin);
}
#ifdef __cplusplus
}
#endif
