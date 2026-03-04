// Lean compiler output
// Module: Lean.Compiler.LCNF.CompatibleTypes
// Imports: public import Lean.Compiler.LCNF.InferType
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
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0;
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Level_isEquiv(x_6, x_8);
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_10; uint8_t x_43; 
x_43 = l_Lean_Expr_isErased(x_1);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Expr_isErased(x_2);
x_10 = x_44;
goto block_42;
}
else
{
x_10 = x_43;
goto block_42;
}
block_9:
{
uint8_t x_7; 
x_7 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_3, x_5);
if (x_7 == 0)
{
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_7;
}
else
{
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
block_42:
{
uint8_t x_11; 
x_11 = 1;
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc_ref(x_1);
x_12 = l_Lean_Expr_headBeta(x_1);
lean_inc_ref(x_2);
x_13 = l_Lean_Expr_headBeta(x_2);
x_14 = lean_expr_eqv(x_1, x_12);
if (x_14 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_12;
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = lean_expr_eqv(x_2, x_13);
if (x_16 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_12;
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_18 = lean_expr_eqv(x_1, x_2);
if (x_18 == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_2);
x_23 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_19, x_21);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_20);
return x_23;
}
else
{
x_1 = x_20;
x_2 = x_22;
goto _start;
}
}
else
{
lean_dec_ref(x_1);
lean_dec_ref(x_2);
return x_18;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_26);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_2);
x_3 = x_25;
x_4 = x_26;
x_5 = x_27;
x_6 = x_28;
goto block_9;
}
else
{
lean_dec_ref(x_1);
lean_dec_ref(x_2);
return x_18;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_30);
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_32);
lean_dec_ref(x_2);
x_3 = x_29;
x_4 = x_30;
x_5 = x_31;
x_6 = x_32;
goto block_9;
}
else
{
lean_dec_ref(x_1);
lean_dec_ref(x_2);
return x_18;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec_ref(x_1);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec_ref(x_2);
x_35 = l_Lean_Level_isEquiv(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
return x_35;
}
else
{
lean_dec_ref(x_1);
lean_dec_ref(x_2);
return x_18;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_dec_ref(x_2);
x_40 = lean_name_eq(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
if (x_40 == 0)
{
lean_dec(x_39);
lean_dec(x_37);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
return x_41;
}
}
else
{
lean_dec_ref(x_1);
lean_dec_ref(x_2);
return x_18;
}
}
default: 
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_1);
x_8 = l_Lean_Compiler_LCNF_InferType_Pure_inferType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_28; 
x_9 = lean_ctor_get(x_8, 0);
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
x_10 = x_8;
x_11 = x_28;
goto block_27;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_headBeta(x_9);
if (lean_obj_tag(x_12) == 7)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 8);
lean_dec_ref(x_12);
x_16 = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0, &l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0);
x_17 = l_Lean_Expr_app___override(x_1, x_16);
x_18 = l_Lean_Expr_lam___override(x_13, x_14, x_17, x_15);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_19);
x_20 = x_10;
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
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_12);
lean_dec_ref(x_1);
x_23 = lean_box(0);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_23);
x_24 = x_10;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
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
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_8, 0);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
x_30 = x_8;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_35; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
x_7 = x_4;
x_8 = x_35;
goto block_34;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_32; 
x_9 = lean_st_ref_take(x_1);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 3);
x_13 = lean_ctor_get(x_9, 4);
x_14 = lean_ctor_get(x_9, 5);
x_15 = lean_ctor_get(x_9, 6);
x_16 = lean_ctor_get(x_9, 7);
x_17 = lean_ctor_get(x_9, 8);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_9, 2);
lean_dec(x_33);
x_18 = x_9;
x_19 = x_32;
goto block_31;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Name_num___override(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_22);
x_23 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_22);
x_23 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_24; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 2, x_23);
x_24 = x_18;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_12);
lean_ctor_set(x_28, 4, x_13);
lean_ctor_set(x_28, 5, x_14);
lean_ctor_set(x_28, 6, x_15);
lean_ctor_set(x_28, 7, x_16);
lean_ctor_set(x_28, 8, x_17);
x_24 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_st_ref_set(x_1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_20);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(x_5);
x_8 = lean_ctor_get(x_7, 0);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
x_9 = x_7;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_93; uint8_t x_156; 
x_156 = l_Lean_Expr_isErased(x_1);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = l_Lean_Expr_isErased(x_2);
x_93 = x_157;
goto block_155;
}
else
{
x_93 = x_156;
goto block_155;
}
block_40:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_10);
x_21 = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(x_10, x_13, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_21;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_21);
x_24 = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_25);
x_26 = l_Lean_Expr_fvar___override(x_25);
x_27 = 0;
x_28 = l_Lean_LocalContext_mkLocalDecl(x_15, x_25, x_9, x_10, x_12, x_27);
x_29 = lean_expr_instantiate1(x_11, x_26);
lean_dec_ref(x_11);
x_30 = lean_expr_instantiate1(x_14, x_26);
lean_dec_ref(x_26);
lean_dec_ref(x_14);
x_1 = x_29;
x_2 = x_30;
x_3 = x_28;
x_4 = x_16;
x_5 = x_17;
x_6 = x_18;
x_7 = x_19;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_32 = lean_ctor_get(x_24, 0);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
x_33 = x_24;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
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
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_21;
}
}
block_92:
{
uint8_t x_48; 
x_48 = l_Lean_Expr_isLambda(x_1);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Expr_isLambda(x_2);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
else
{
lean_object* x_52; 
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc_ref(x_42);
x_52 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(x_1, x_42, x_43, x_44, x_45, x_46);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_63; 
x_53 = lean_ctor_get(x_52, 0);
x_63 = !lean_is_exclusive(x_52);
if (x_63 == 0)
{
x_54 = x_52;
x_55 = x_63;
goto block_62;
}
else
{
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = x_63;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_56; 
lean_del_object(x_54);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec_ref(x_53);
x_1 = x_56;
x_3 = x_42;
x_4 = x_43;
x_5 = x_44;
x_6 = x_45;
x_7 = x_46;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_53);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_2);
x_58 = lean_box(x_48);
if (x_55 == 0)
{
lean_ctor_set(x_54, 0, x_58);
x_59 = x_54;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
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
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_2);
x_64 = lean_ctor_get(x_52, 0);
x_71 = !lean_is_exclusive(x_52);
if (x_71 == 0)
{
x_65 = x_52;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_52);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
}
else
{
lean_object* x_72; 
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc_ref(x_42);
x_72 = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(x_2, x_42, x_43, x_44, x_45, x_46);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_83; 
x_73 = lean_ctor_get(x_72, 0);
x_83 = !lean_is_exclusive(x_72);
if (x_83 == 0)
{
x_74 = x_72;
x_75 = x_83;
goto block_82;
}
else
{
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = x_83;
goto block_82;
}
block_82:
{
if (lean_obj_tag(x_73) == 1)
{
lean_object* x_76; 
lean_del_object(x_74);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
lean_dec_ref(x_73);
x_2 = x_76;
x_3 = x_42;
x_4 = x_43;
x_5 = x_44;
x_6 = x_45;
x_7 = x_46;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_73);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_1);
x_78 = lean_box(x_41);
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_78);
x_79 = x_74;
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
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_1);
x_84 = lean_ctor_get(x_72, 0);
x_91 = !lean_is_exclusive(x_72);
if (x_91 == 0)
{
x_85 = x_72;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_72);
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
block_155:
{
uint8_t x_94; 
x_94 = 1;
if (x_93 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_inc_ref(x_1);
x_95 = l_Lean_Expr_headBeta(x_1);
lean_inc_ref(x_2);
x_96 = l_Lean_Expr_headBeta(x_2);
x_97 = lean_expr_eqv(x_1, x_95);
if (x_97 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_95;
x_2 = x_96;
goto _start;
}
else
{
uint8_t x_99; 
x_99 = lean_expr_eqv(x_2, x_96);
if (x_99 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1 = x_95;
x_2 = x_96;
goto _start;
}
else
{
uint8_t x_101; 
lean_dec_ref(x_96);
lean_dec_ref(x_95);
x_101 = lean_expr_eqv(x_1, x_2);
if (x_101 == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_103);
lean_dec_ref(x_1);
x_104 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_105);
lean_dec_ref(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_106 = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(x_102, x_104, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_dec_ref(x_105);
lean_dec_ref(x_103);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_106;
}
else
{
lean_dec_ref(x_106);
x_1 = x_103;
x_2 = x_105;
goto _start;
}
}
else
{
lean_dec_ref(x_105);
lean_dec_ref(x_103);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_106;
}
}
case 10:
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_110);
lean_dec_ref(x_2);
x_2 = x_110;
goto _start;
}
default: 
{
x_41 = x_101;
x_42 = x_3;
x_43 = x_4;
x_44 = x_5;
x_45 = x_6;
x_46 = x_7;
x_47 = lean_box(0);
goto block_92;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_1, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_114);
x_115 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_116 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_117);
lean_dec_ref(x_2);
x_9 = x_112;
x_10 = x_113;
x_11 = x_114;
x_12 = x_115;
x_13 = x_116;
x_14 = x_117;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = lean_box(0);
goto block_40;
}
case 10:
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_118);
lean_dec_ref(x_2);
x_2 = x_118;
goto _start;
}
default: 
{
x_41 = x_101;
x_42 = x_3;
x_43 = x_4;
x_44 = x_5;
x_45 = x_6;
x_46 = x_7;
x_47 = lean_box(0);
goto block_92;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_122);
x_123 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_124 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_125);
lean_dec_ref(x_2);
x_9 = x_120;
x_10 = x_121;
x_11 = x_122;
x_12 = x_123;
x_13 = x_124;
x_14 = x_125;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = lean_box(0);
goto block_40;
}
case 10:
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_126);
lean_dec_ref(x_2);
x_2 = x_126;
goto _start;
}
default: 
{
x_41 = x_101;
x_42 = x_3;
x_43 = x_4;
x_44 = x_5;
x_45 = x_6;
x_46 = x_7;
x_47 = lean_box(0);
goto block_92;
}
}
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_128 = lean_ctor_get(x_1, 0);
lean_inc(x_128);
lean_dec_ref(x_1);
x_129 = lean_ctor_get(x_2, 0);
lean_inc(x_129);
lean_dec_ref(x_2);
x_130 = l_Lean_Level_isEquiv(x_128, x_129);
lean_dec(x_129);
lean_dec(x_128);
x_131 = lean_box(x_130);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
case 10:
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_133);
lean_dec_ref(x_2);
x_2 = x_133;
goto _start;
}
default: 
{
x_41 = x_101;
x_42 = x_3;
x_43 = x_4;
x_44 = x_5;
x_45 = x_6;
x_46 = x_7;
x_47 = lean_box(0);
goto block_92;
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_135 = lean_ctor_get(x_1, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_1, 1);
lean_inc(x_136);
lean_dec_ref(x_1);
x_137 = lean_ctor_get(x_2, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_2, 1);
lean_inc(x_138);
lean_dec_ref(x_2);
x_139 = lean_name_eq(x_135, x_137);
lean_dec(x_137);
lean_dec(x_135);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_138);
lean_dec(x_136);
x_140 = lean_box(x_139);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
else
{
uint8_t x_142; lean_object* x_143; lean_object* x_144; 
x_142 = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(x_136, x_138);
lean_dec(x_138);
lean_dec(x_136);
x_143 = lean_box(x_142);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
case 10:
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_145);
lean_dec_ref(x_2);
x_2 = x_145;
goto _start;
}
default: 
{
x_41 = x_101;
x_42 = x_3;
x_43 = x_4;
x_44 = x_5;
x_45 = x_6;
x_46 = x_7;
x_47 = lean_box(0);
goto block_92;
}
}
}
case 10:
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_147);
lean_dec_ref(x_1);
x_1 = x_147;
goto _start;
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_149);
lean_dec_ref(x_2);
x_2 = x_149;
goto _start;
}
else
{
x_41 = x_101;
x_42 = x_3;
x_43 = x_4;
x_44 = x_5;
x_45 = x_6;
x_46 = x_7;
x_47 = lean_box(0);
goto block_92;
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_151 = lean_box(x_94);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_153 = lean_box(x_94);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Lean_Compiler_LCNF_compatibleTypesQuick(x_1, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_InferType(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
}
#ifdef __cplusplus
}
#endif
