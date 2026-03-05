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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_317; 
x_23 = lean_ctor_get(x_22, 0);
x_317 = !lean_is_exclusive(x_22);
if (x_317 == 0)
{
x_24 = x_22;
x_25 = x_317;
goto block_316;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_317;
goto block_316;
}
block_316:
{
lean_object* x_26; 
x_26 = l_isCtorIdx_x3f___redArg(x_23, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_307; 
x_27 = lean_ctor_get(x_26, 0);
x_307 = !lean_is_exclusive(x_26);
if (x_307 == 0)
{
x_28 = x_26;
x_29 = x_307;
goto block_306;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_307;
goto block_306;
}
block_306:
{
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_301; 
x_30 = lean_ctor_get(x_27, 0);
x_301 = !lean_is_exclusive(x_27);
if (x_301 == 0)
{
x_31 = x_27;
x_32 = x_301;
goto block_300;
}
else
{
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = x_301;
goto block_300;
}
block_300:
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
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_del_object(x_28);
x_45 = l_Lean_instInhabitedExpr;
x_46 = lean_nat_sub(x_36, x_38);
x_47 = lean_array_get(x_45, x_3, x_46);
lean_dec(x_46);
lean_dec_ref(x_3);
lean_inc(x_47);
x_48 = l_Lean_Meta_Grind_getRootENode___redArg(x_47, x_5, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_291; 
x_49 = lean_ctor_get(x_48, 0);
x_291 = !lean_is_exclusive(x_48);
if (x_291 == 0)
{
x_50 = x_48;
x_51 = x_291;
goto block_290;
}
else
{
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = x_291;
goto block_290;
}
block_290:
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_52);
x_53 = lean_ctor_get_uint8(x_49, sizeof(void*)*11 + 2);
x_54 = lean_ctor_get_uint8(x_49, sizeof(void*)*11 + 4);
lean_dec(x_49);
if (x_53 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec_ref(x_52);
lean_dec(x_47);
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
x_112 = lean_box(0);
if (x_51 == 0)
{
lean_ctor_set(x_50, 0, x_112);
x_113 = x_50;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_112);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
else
{
lean_object* x_116; 
lean_del_object(x_50);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_52);
x_116 = l_Lean_Meta_isConstructorApp_x3f(x_52, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_281; 
x_117 = lean_ctor_get(x_116, 0);
x_281 = !lean_is_exclusive(x_116);
if (x_281 == 0)
{
x_118 = x_116;
x_119 = x_281;
goto block_280;
}
else
{
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_box(0);
x_119 = x_281;
goto block_280;
}
block_280:
{
if (lean_obj_tag(x_117) == 1)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_del_object(x_118);
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
lean_dec_ref(x_117);
if (x_54 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
x_121 = x_5;
x_122 = x_6;
x_123 = x_7;
x_124 = x_8;
x_125 = x_9;
x_126 = x_10;
x_127 = x_11;
x_128 = x_12;
x_129 = x_13;
x_130 = x_14;
x_131 = lean_box(0);
goto block_181;
}
else
{
lean_object* x_182; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_52);
lean_inc(x_47);
x_182 = l_Lean_Meta_Grind_hasSameType(x_47, x_52, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = lean_unbox(x_183);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; 
lean_dec(x_120);
lean_dec_ref(x_1);
x_185 = l_Lean_Meta_Grind_getGeneration___redArg(x_47, x_5);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec_ref(x_185);
x_187 = l_Lean_Meta_Grind_getGeneration___redArg(x_52, x_5);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_251; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_251 = lean_nat_dec_le(x_186, x_188);
if (x_251 == 0)
{
lean_dec(x_188);
x_189 = x_186;
goto block_250;
}
else
{
lean_dec(x_186);
x_189 = x_188;
goto block_250;
}
block_250:
{
lean_object* x_190; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_47);
x_190 = lean_infer_type(x_47, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_192 = l_Lean_Meta_whnfD(x_191, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec_ref(x_192);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_52);
x_194 = lean_infer_type(x_52, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec_ref(x_194);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_196 = l_Lean_Meta_whnfD(x_195, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_217; 
x_197 = lean_ctor_get(x_196, 0);
x_217 = !lean_is_exclusive(x_196);
if (x_217 == 0)
{
x_198 = x_196;
x_199 = x_217;
goto block_216;
}
else
{
lean_inc(x_197);
lean_dec(x_196);
x_198 = lean_box(0);
x_199 = x_217;
goto block_216;
}
block_216:
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_ctor_get(x_33, 0);
lean_inc(x_200);
lean_dec_ref(x_33);
lean_inc(x_37);
x_201 = l_Lean_Expr_isAppOfArity(x_193, x_200, x_37);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_200);
lean_del_object(x_198);
lean_dec(x_197);
lean_dec(x_193);
lean_dec(x_189);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_del_object(x_31);
lean_del_object(x_24);
x_202 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
x_203 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_202, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_203;
}
else
{
uint8_t x_204; 
x_204 = l_Lean_Expr_isAppOfArity(x_197, x_200, x_37);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_200);
lean_dec(x_197);
lean_dec(x_193);
lean_dec(x_189);
lean_dec_ref(x_52);
lean_dec(x_47);
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
x_205 = lean_box(0);
if (x_199 == 0)
{
lean_ctor_set(x_198, 0, x_205);
x_206 = x_198;
goto block_207;
}
else
{
lean_object* x_208; 
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_205);
x_206 = x_208;
goto block_207;
}
block_207:
{
return x_206;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
lean_del_object(x_198);
x_209 = lean_st_ref_get(x_14);
x_210 = lean_ctor_get(x_209, 0);
lean_inc_ref(x_210);
lean_dec(x_209);
x_211 = l_Lean_Expr_getAppFn(x_193);
x_212 = l_Lean_Expr_constLevels_x21(x_211);
lean_dec_ref(x_211);
x_213 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_200);
x_214 = l_Lean_Environment_containsOnBranch(x_210, x_213);
if (x_214 == 0)
{
lean_object* x_215; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_213);
x_215 = l_Lean_executeReservedNameAction(x_213, x_13, x_14);
if (lean_obj_tag(x_215) == 0)
{
lean_dec_ref(x_215);
x_55 = x_193;
x_56 = x_189;
x_57 = x_197;
x_58 = x_213;
x_59 = x_212;
x_60 = x_5;
x_61 = x_6;
x_62 = x_7;
x_63 = x_8;
x_64 = x_9;
x_65 = x_10;
x_66 = x_11;
x_67 = x_12;
x_68 = x_13;
x_69 = x_14;
x_70 = lean_box(0);
goto block_111;
}
else
{
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_197);
lean_dec(x_193);
lean_dec(x_189);
lean_dec_ref(x_52);
lean_dec(x_47);
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
return x_215;
}
}
else
{
x_55 = x_193;
x_56 = x_189;
x_57 = x_197;
x_58 = x_213;
x_59 = x_212;
x_60 = x_5;
x_61 = x_6;
x_62 = x_7;
x_63 = x_8;
x_64 = x_9;
x_65 = x_10;
x_66 = x_11;
x_67 = x_12;
x_68 = x_13;
x_69 = x_14;
x_70 = lean_box(0);
goto block_111;
}
}
}
}
}
else
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; uint8_t x_225; 
lean_dec(x_193);
lean_dec(x_189);
lean_dec_ref(x_52);
lean_dec(x_47);
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
x_218 = lean_ctor_get(x_196, 0);
x_225 = !lean_is_exclusive(x_196);
if (x_225 == 0)
{
x_219 = x_196;
x_220 = x_225;
goto block_224;
}
else
{
lean_inc(x_218);
lean_dec(x_196);
x_219 = lean_box(0);
x_220 = x_225;
goto block_224;
}
block_224:
{
lean_object* x_221; 
if (x_220 == 0)
{
x_221 = x_219;
goto block_222;
}
else
{
lean_object* x_223; 
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_218);
x_221 = x_223;
goto block_222;
}
block_222:
{
return x_221;
}
}
}
}
else
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_233; 
lean_dec(x_193);
lean_dec(x_189);
lean_dec_ref(x_52);
lean_dec(x_47);
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
x_226 = lean_ctor_get(x_194, 0);
x_233 = !lean_is_exclusive(x_194);
if (x_233 == 0)
{
x_227 = x_194;
x_228 = x_233;
goto block_232;
}
else
{
lean_inc(x_226);
lean_dec(x_194);
x_227 = lean_box(0);
x_228 = x_233;
goto block_232;
}
block_232:
{
lean_object* x_229; 
if (x_228 == 0)
{
x_229 = x_227;
goto block_230;
}
else
{
lean_object* x_231; 
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_226);
x_229 = x_231;
goto block_230;
}
block_230:
{
return x_229;
}
}
}
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; uint8_t x_241; 
lean_dec(x_189);
lean_dec_ref(x_52);
lean_dec(x_47);
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
x_234 = lean_ctor_get(x_192, 0);
x_241 = !lean_is_exclusive(x_192);
if (x_241 == 0)
{
x_235 = x_192;
x_236 = x_241;
goto block_240;
}
else
{
lean_inc(x_234);
lean_dec(x_192);
x_235 = lean_box(0);
x_236 = x_241;
goto block_240;
}
block_240:
{
lean_object* x_237; 
if (x_236 == 0)
{
x_237 = x_235;
goto block_238;
}
else
{
lean_object* x_239; 
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_234);
x_237 = x_239;
goto block_238;
}
block_238:
{
return x_237;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_249; 
lean_dec(x_189);
lean_dec_ref(x_52);
lean_dec(x_47);
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
x_242 = lean_ctor_get(x_190, 0);
x_249 = !lean_is_exclusive(x_190);
if (x_249 == 0)
{
x_243 = x_190;
x_244 = x_249;
goto block_248;
}
else
{
lean_inc(x_242);
lean_dec(x_190);
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
lean_object* x_252; lean_object* x_253; uint8_t x_254; uint8_t x_259; 
lean_dec(x_186);
lean_dec_ref(x_52);
lean_dec(x_47);
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
x_252 = lean_ctor_get(x_187, 0);
x_259 = !lean_is_exclusive(x_187);
if (x_259 == 0)
{
x_253 = x_187;
x_254 = x_259;
goto block_258;
}
else
{
lean_inc(x_252);
lean_dec(x_187);
x_253 = lean_box(0);
x_254 = x_259;
goto block_258;
}
block_258:
{
lean_object* x_255; 
if (x_254 == 0)
{
x_255 = x_253;
goto block_256;
}
else
{
lean_object* x_257; 
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_252);
x_255 = x_257;
goto block_256;
}
block_256:
{
return x_255;
}
}
}
}
else
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; uint8_t x_267; 
lean_dec_ref(x_52);
lean_dec(x_47);
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
x_260 = lean_ctor_get(x_185, 0);
x_267 = !lean_is_exclusive(x_185);
if (x_267 == 0)
{
x_261 = x_185;
x_262 = x_267;
goto block_266;
}
else
{
lean_inc(x_260);
lean_dec(x_185);
x_261 = lean_box(0);
x_262 = x_267;
goto block_266;
}
block_266:
{
lean_object* x_263; 
if (x_262 == 0)
{
x_263 = x_261;
goto block_264;
}
else
{
lean_object* x_265; 
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_260);
x_263 = x_265;
goto block_264;
}
block_264:
{
return x_263;
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
x_121 = x_5;
x_122 = x_6;
x_123 = x_7;
x_124 = x_8;
x_125 = x_9;
x_126 = x_10;
x_127 = x_11;
x_128 = x_12;
x_129 = x_13;
x_130 = x_14;
x_131 = lean_box(0);
goto block_181;
}
}
else
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; uint8_t x_275; 
lean_dec(x_120);
lean_dec_ref(x_52);
lean_dec(x_47);
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
x_268 = lean_ctor_get(x_182, 0);
x_275 = !lean_is_exclusive(x_182);
if (x_275 == 0)
{
x_269 = x_182;
x_270 = x_275;
goto block_274;
}
else
{
lean_inc(x_268);
lean_dec(x_182);
x_269 = lean_box(0);
x_270 = x_275;
goto block_274;
}
block_274:
{
lean_object* x_271; 
if (x_270 == 0)
{
x_271 = x_269;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_268);
x_271 = x_273;
goto block_272;
}
block_272:
{
return x_271;
}
}
}
}
block_181:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_120, 2);
lean_inc(x_132);
lean_dec(x_120);
x_133 = l_Lean_mkNatLit(x_132);
x_134 = l_Lean_Meta_Sym_shareCommon___redArg(x_133, x_126);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_box(0);
lean_inc(x_130);
lean_inc_ref(x_129);
lean_inc(x_128);
lean_inc_ref(x_127);
lean_inc(x_126);
lean_inc_ref(x_125);
lean_inc(x_124);
lean_inc_ref(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_135);
x_138 = lean_grind_internalize(x_135, x_136, x_137, x_121, x_122, x_123, x_124, x_125, x_126, x_127, x_128, x_129, x_130);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
lean_dec_ref(x_138);
lean_inc(x_130);
lean_inc_ref(x_129);
lean_inc(x_128);
lean_inc_ref(x_127);
lean_inc_ref(x_123);
lean_inc(x_121);
x_139 = lean_grind_mk_eq_proof(x_47, x_52, x_121, x_122, x_123, x_124, x_125, x_126, x_127, x_128, x_129, x_130);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_130);
lean_inc_ref(x_129);
lean_inc(x_128);
lean_inc_ref(x_127);
x_142 = l_Lean_Meta_mkCongrArg(x_141, x_140, x_127, x_128, x_129, x_130);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
lean_inc(x_130);
lean_inc_ref(x_129);
lean_inc(x_128);
lean_inc_ref(x_127);
lean_inc(x_135);
lean_inc_ref(x_1);
x_144 = l_Lean_Meta_mkEq(x_1, x_135, x_127, x_128, x_129, x_130);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = l_Lean_Meta_mkExpectedPropHint(x_143, x_145);
x_147 = 0;
x_148 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_135, x_146, x_147, x_121, x_123, x_127, x_128, x_129, x_130);
lean_dec_ref(x_123);
lean_dec(x_121);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_156; 
lean_dec(x_143);
lean_dec(x_135);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec_ref(x_123);
lean_dec(x_121);
lean_dec_ref(x_1);
x_149 = lean_ctor_get(x_144, 0);
x_156 = !lean_is_exclusive(x_144);
if (x_156 == 0)
{
x_150 = x_144;
x_151 = x_156;
goto block_155;
}
else
{
lean_inc(x_149);
lean_dec(x_144);
x_150 = lean_box(0);
x_151 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_152; 
if (x_151 == 0)
{
x_152 = x_150;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_149);
x_152 = x_154;
goto block_153;
}
block_153:
{
return x_152;
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_164; 
lean_dec(x_135);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec_ref(x_123);
lean_dec(x_121);
lean_dec_ref(x_1);
x_157 = lean_ctor_get(x_142, 0);
x_164 = !lean_is_exclusive(x_142);
if (x_164 == 0)
{
x_158 = x_142;
x_159 = x_164;
goto block_163;
}
else
{
lean_inc(x_157);
lean_dec(x_142);
x_158 = lean_box(0);
x_159 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_160; 
if (x_159 == 0)
{
x_160 = x_158;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_157);
x_160 = x_162;
goto block_161;
}
block_161:
{
return x_160;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_172; 
lean_dec(x_135);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec_ref(x_123);
lean_dec(x_121);
lean_dec_ref(x_1);
x_165 = lean_ctor_get(x_139, 0);
x_172 = !lean_is_exclusive(x_139);
if (x_172 == 0)
{
x_166 = x_139;
x_167 = x_172;
goto block_171;
}
else
{
lean_inc(x_165);
lean_dec(x_139);
x_166 = lean_box(0);
x_167 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_168; 
if (x_167 == 0)
{
x_168 = x_166;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_165);
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
lean_dec(x_135);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec_ref(x_1);
return x_138;
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_180; 
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec_ref(x_1);
x_173 = lean_ctor_get(x_134, 0);
x_180 = !lean_is_exclusive(x_134);
if (x_180 == 0)
{
x_174 = x_134;
x_175 = x_180;
goto block_179;
}
else
{
lean_inc(x_173);
lean_dec(x_134);
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
lean_object* x_276; lean_object* x_277; 
lean_dec(x_117);
lean_dec_ref(x_52);
lean_dec(x_47);
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
x_276 = lean_box(0);
if (x_119 == 0)
{
lean_ctor_set(x_118, 0, x_276);
x_277 = x_118;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_279, 0, x_276);
x_277 = x_279;
goto block_278;
}
block_278:
{
return x_277;
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; uint8_t x_289; 
lean_dec_ref(x_52);
lean_dec(x_47);
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
x_282 = lean_ctor_get(x_116, 0);
x_289 = !lean_is_exclusive(x_116);
if (x_289 == 0)
{
x_283 = x_116;
x_284 = x_289;
goto block_288;
}
else
{
lean_inc(x_282);
lean_dec(x_116);
x_283 = lean_box(0);
x_284 = x_289;
goto block_288;
}
block_288:
{
lean_object* x_285; 
if (x_284 == 0)
{
x_285 = x_283;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_282);
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
block_111:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_inc(x_58);
x_71 = l_Lean_mkConst(x_58, x_59);
x_72 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
x_73 = l_Lean_Expr_getAppNumArgs(x_55);
lean_inc(x_73);
x_74 = lean_mk_array(x_73, x_72);
x_75 = lean_nat_sub(x_73, x_38);
lean_dec(x_73);
x_76 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_55, x_74, x_75);
x_77 = l_Lean_mkAppN(x_71, x_76);
lean_dec_ref(x_76);
x_78 = l_Lean_Expr_app___override(x_77, x_47);
x_79 = l_Lean_Expr_getAppNumArgs(x_57);
lean_inc(x_79);
x_80 = lean_mk_array(x_79, x_72);
x_81 = lean_nat_sub(x_79, x_38);
lean_dec(x_79);
x_82 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_57, x_80, x_81);
x_83 = l_Lean_mkAppN(x_78, x_82);
lean_dec_ref(x_82);
x_84 = l_Lean_Expr_app___override(x_83, x_52);
lean_inc(x_69);
lean_inc_ref(x_68);
lean_inc(x_67);
lean_inc_ref(x_66);
lean_inc_ref(x_84);
x_85 = lean_infer_type(x_84, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
if (x_32 == 0)
{
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_58);
x_87 = x_31;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_58);
x_87 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_88; 
if (x_25 == 0)
{
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 0, x_87);
x_88 = x_24;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(x_100, 0, x_87);
x_88 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_89; 
x_89 = l_Lean_Meta_Grind_addNewRawFact(x_84, x_86, x_56, x_88, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec(x_60);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; uint8_t x_97; 
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_89, 0);
lean_dec(x_98);
x_90 = x_89;
x_91 = x_97;
goto block_96;
}
else
{
lean_dec(x_89);
x_90 = lean_box(0);
x_91 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_box(0);
if (x_91 == 0)
{
lean_ctor_set(x_90, 0, x_92);
x_93 = x_90;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
else
{
return x_89;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_dec_ref(x_84);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_56);
lean_del_object(x_31);
lean_del_object(x_24);
x_103 = lean_ctor_get(x_85, 0);
x_110 = !lean_is_exclusive(x_85);
if (x_110 == 0)
{
x_104 = x_85;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_dec(x_85);
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
}
}
else
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_299; 
lean_dec(x_47);
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
x_292 = lean_ctor_get(x_48, 0);
x_299 = !lean_is_exclusive(x_48);
if (x_299 == 0)
{
x_293 = x_48;
x_294 = x_299;
goto block_298;
}
else
{
lean_inc(x_292);
lean_dec(x_48);
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
}
}
else
{
lean_object* x_302; lean_object* x_303; 
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
x_302 = lean_box(0);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_302);
x_303 = x_28;
goto block_304;
}
else
{
lean_object* x_305; 
x_305 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_305, 0, x_302);
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
x_308 = lean_ctor_get(x_26, 0);
x_315 = !lean_is_exclusive(x_26);
if (x_315 == 0)
{
x_309 = x_26;
x_310 = x_315;
goto block_314;
}
else
{
lean_inc(x_308);
lean_dec(x_26);
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
}
}
else
{
lean_object* x_318; lean_object* x_319; 
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
x_318 = lean_box(0);
x_319 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_319, 0, x_318);
return x_319;
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
