// Lean compiler output
// Module: Lean.Meta.Sym.MaxFVar
// Imports: public import Lean.Meta.Sym.SymM
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Meta.Sym.MaxFVar"};
static const lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.Sym.getMaxFVar\?"};
static const lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(lean_object* v_fvarId1_x3f_1_, lean_object* v_fvarId2_x3f_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
if (lean_obj_tag(v_fvarId1_x3f_1_) == 1)
{
if (lean_obj_tag(v_fvarId2_x3f_2_) == 1)
{
lean_object* v_val_7_; lean_object* v_val_8_; uint8_t v___x_9_; 
v_val_7_ = lean_ctor_get(v_fvarId1_x3f_1_, 0);
v_val_8_ = lean_ctor_get(v_fvarId2_x3f_2_, 0);
v___x_9_ = l_Lean_instBEqFVarId_beq(v_val_7_, v_val_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_inc(v_val_7_);
v___x_10_ = l_Lean_FVarId_getDecl___redArg(v_val_7_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_a_11_);
lean_dec_ref(v___x_10_);
lean_inc(v_val_8_);
v___x_12_ = l_Lean_FVarId_getDecl___redArg(v_val_8_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_26_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_26_ == 0)
{
v___x_15_ = v___x_12_;
v_isShared_16_ = v_isSharedCheck_26_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_a_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_26_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_17_ = l_Lean_LocalDecl_index(v_a_13_);
lean_dec(v_a_13_);
v___x_18_ = l_Lean_LocalDecl_index(v_a_11_);
lean_dec(v_a_11_);
v___x_19_ = lean_nat_dec_lt(v___x_17_, v___x_18_);
lean_dec(v___x_18_);
lean_dec(v___x_17_);
if (v___x_19_ == 0)
{
lean_object* v___x_21_; 
lean_dec_ref(v_fvarId1_x3f_1_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v_fvarId2_x3f_2_);
v___x_21_ = v___x_15_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_fvarId2_x3f_2_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
else
{
lean_object* v___x_24_; 
lean_dec_ref(v_fvarId2_x3f_2_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v_fvarId1_x3f_1_);
v___x_24_ = v___x_15_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_fvarId1_x3f_1_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
else
{
lean_object* v_a_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_34_; 
lean_dec(v_a_11_);
lean_dec_ref(v_fvarId2_x3f_2_);
lean_dec_ref(v_fvarId1_x3f_1_);
v_a_27_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_34_ == 0)
{
v___x_29_ = v___x_12_;
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_a_27_);
lean_dec(v___x_12_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_a_27_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
else
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_42_; 
lean_dec_ref(v_fvarId2_x3f_2_);
lean_dec_ref(v_fvarId1_x3f_1_);
v_a_35_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_42_ == 0)
{
v___x_37_ = v___x_10_;
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_10_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_35_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
else
{
lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
v_isSharedCheck_49_ = !lean_is_exclusive(v_fvarId2_x3f_2_);
if (v_isSharedCheck_49_ == 0)
{
lean_object* v_unused_50_; 
v_unused_50_ = lean_ctor_get(v_fvarId2_x3f_2_, 0);
lean_dec(v_unused_50_);
v___x_44_ = v_fvarId2_x3f_2_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_dec(v_fvarId2_x3f_2_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
lean_ctor_set_tag(v___x_44_, 0);
lean_ctor_set(v___x_44_, 0, v_fvarId1_x3f_1_);
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_fvarId1_x3f_1_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
else
{
lean_object* v___x_51_; 
lean_dec(v_fvarId2_x3f_2_);
v___x_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_51_, 0, v_fvarId1_x3f_1_);
return v___x_51_;
}
}
else
{
lean_object* v___x_52_; 
lean_dec(v_fvarId1_x3f_1_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v_fvarId2_x3f_2_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg___boxed(lean_object* v_fvarId1_x3f_53_, lean_object* v_fvarId2_x3f_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_fvarId1_x3f_53_, v_fvarId2_x3f_54_, v_a_55_, v_a_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec_ref(v_a_55_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(lean_object* v_fvarId1_x3f_60_, lean_object* v_fvarId2_x3f_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_fvarId1_x3f_60_, v_fvarId2_x3f_61_, v_a_62_, v_a_64_, v_a_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___boxed(lean_object* v_fvarId1_x3f_68_, lean_object* v_fvarId2_x3f_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(v_fvarId1_x3f_68_, v_fvarId2_x3f_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(lean_object* v_e_78_, lean_object* v_k_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
uint8_t v___y_88_; uint8_t v___x_133_; 
v___x_133_ = l_Lean_Expr_hasFVar(v_e_78_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
v___x_134_ = l_Lean_Expr_hasMVar(v_e_78_);
v___y_88_ = v___x_134_;
goto v___jp_87_;
}
else
{
v___y_88_ = v___x_133_;
goto v___jp_87_;
}
v___jp_87_:
{
if (v___y_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec_ref(v_k_79_);
lean_dec_ref(v_e_78_);
v___x_89_ = lean_box(0);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v_maxFVar_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; 
v___x_91_ = lean_st_ref_get(v_a_81_);
v_maxFVar_92_ = lean_ctor_get(v___x_91_, 1);
lean_inc_ref(v_maxFVar_92_);
lean_dec(v___x_91_);
v___f_93_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0));
v___f_94_ = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1));
lean_inc_ref(v_e_78_);
v___x_95_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_93_, v___f_94_, v_maxFVar_92_, v_e_78_);
if (lean_obj_tag(v___x_95_) == 1)
{
lean_object* v_val_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec_ref(v_k_79_);
lean_dec_ref(v_e_78_);
v_val_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_val_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set_tag(v___x_98_, 0);
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_val_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
else
{
lean_object* v___x_104_; 
lean_dec(v___x_95_);
lean_inc(v_a_85_);
lean_inc_ref(v_a_84_);
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
lean_inc(v_a_81_);
lean_inc_ref(v_a_80_);
v___x_104_ = lean_apply_7(v_k_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, lean_box(0));
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_132_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_132_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_132_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_132_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v_share_110_; lean_object* v_maxFVar_111_; lean_object* v_proofInstInfo_112_; lean_object* v_inferType_113_; lean_object* v_getLevel_114_; lean_object* v_congrInfo_115_; lean_object* v_defEqI_116_; lean_object* v_extensions_117_; lean_object* v_issues_118_; uint8_t v_debug_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_131_; 
v___x_109_ = lean_st_ref_take(v_a_81_);
v_share_110_ = lean_ctor_get(v___x_109_, 0);
v_maxFVar_111_ = lean_ctor_get(v___x_109_, 1);
v_proofInstInfo_112_ = lean_ctor_get(v___x_109_, 2);
v_inferType_113_ = lean_ctor_get(v___x_109_, 3);
v_getLevel_114_ = lean_ctor_get(v___x_109_, 4);
v_congrInfo_115_ = lean_ctor_get(v___x_109_, 5);
v_defEqI_116_ = lean_ctor_get(v___x_109_, 6);
v_extensions_117_ = lean_ctor_get(v___x_109_, 7);
v_issues_118_ = lean_ctor_get(v___x_109_, 8);
v_debug_119_ = lean_ctor_get_uint8(v___x_109_, sizeof(void*)*9);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_131_ == 0)
{
v___x_121_ = v___x_109_;
v_isShared_122_ = v_isSharedCheck_131_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_issues_118_);
lean_inc(v_extensions_117_);
lean_inc(v_defEqI_116_);
lean_inc(v_congrInfo_115_);
lean_inc(v_getLevel_114_);
lean_inc(v_inferType_113_);
lean_inc(v_proofInstInfo_112_);
lean_inc(v_maxFVar_111_);
lean_inc(v_share_110_);
lean_dec(v___x_109_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_131_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
lean_inc(v_a_105_);
v___x_123_ = l_Lean_PersistentHashMap_insert___redArg(v___f_93_, v___f_94_, v_maxFVar_111_, v_e_78_, v_a_105_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_123_);
v___x_125_ = v___x_121_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_share_110_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_130_, 2, v_proofInstInfo_112_);
lean_ctor_set(v_reuseFailAlloc_130_, 3, v_inferType_113_);
lean_ctor_set(v_reuseFailAlloc_130_, 4, v_getLevel_114_);
lean_ctor_set(v_reuseFailAlloc_130_, 5, v_congrInfo_115_);
lean_ctor_set(v_reuseFailAlloc_130_, 6, v_defEqI_116_);
lean_ctor_set(v_reuseFailAlloc_130_, 7, v_extensions_117_);
lean_ctor_set(v_reuseFailAlloc_130_, 8, v_issues_118_);
lean_ctor_set_uint8(v_reuseFailAlloc_130_, sizeof(void*)*9, v_debug_119_);
v___x_125_ = v_reuseFailAlloc_130_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_st_ref_set(v_a_81_, v___x_125_);
if (v_isShared_108_ == 0)
{
v___x_128_ = v___x_107_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_105_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_78_);
return v___x_104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object* v_e_135_, lean_object* v_k_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(v_e_135_, v_k_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
return v_res_144_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0(void){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object* v_msg_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_4706__overap_155_; lean_object* v___x_156_; 
v___x_154_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
v___x_4706__overap_155_ = lean_panic_fn_borrowed(v___x_154_, v_msg_146_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
v___x_156_ = lean_apply_7(v___x_4706__overap_155_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, lean_box(0));
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object* v_msg_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v_msg_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
lean_object* v_ks_170_; lean_object* v_vs_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_195_; 
v_ks_170_ = lean_ctor_get(v_x_166_, 0);
v_vs_171_ = lean_ctor_get(v_x_166_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_195_ == 0)
{
v___x_173_ = v_x_166_;
v_isShared_174_ = v_isSharedCheck_195_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_vs_171_);
lean_inc(v_ks_170_);
lean_dec(v_x_166_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_195_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = lean_array_get_size(v_ks_170_);
v___x_176_ = lean_nat_dec_lt(v_x_167_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
lean_dec(v_x_167_);
v___x_177_ = lean_array_push(v_ks_170_, v_x_168_);
v___x_178_ = lean_array_push(v_vs_171_, v_x_169_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v___x_178_);
lean_ctor_set(v___x_173_, 0, v___x_177_);
v___x_180_ = v___x_173_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
else
{
lean_object* v_k_x27_182_; uint8_t v___x_183_; 
v_k_x27_182_ = lean_array_fget_borrowed(v_ks_170_, v_x_167_);
v___x_183_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_168_, v_k_x27_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_185_; 
if (v_isShared_174_ == 0)
{
v___x_185_ = v___x_173_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_ks_170_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_vs_171_);
v___x_185_ = v_reuseFailAlloc_189_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_x_167_, v___x_186_);
lean_dec(v_x_167_);
v_x_166_ = v___x_185_;
v_x_167_ = v___x_187_;
goto _start;
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_array_fset(v_ks_170_, v_x_167_, v_x_168_);
v___x_191_ = lean_array_fset(v_vs_171_, v_x_167_, v_x_169_);
lean_dec(v_x_167_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v___x_191_);
lean_ctor_set(v___x_173_, 0, v___x_190_);
v___x_193_ = v___x_173_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_n_196_, lean_object* v_k_197_, lean_object* v_v_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_n_196_, v___x_199_, v_k_197_, v_v_198_);
return v___x_200_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; 
v___x_201_ = ((size_t)5ULL);
v___x_202_ = ((size_t)1ULL);
v___x_203_ = lean_usize_shift_left(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_204_; size_t v___x_205_; size_t v___x_206_; 
v___x_204_ = ((size_t)1ULL);
v___x_205_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
v___x_206_ = lean_usize_sub(v___x_205_, v___x_204_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* v_x_208_, size_t v_x_209_, size_t v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v_es_213_; size_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; lean_object* v_j_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_es_213_ = lean_ctor_get(v_x_208_, 0);
v___x_214_ = ((size_t)5ULL);
v___x_215_ = ((size_t)1ULL);
v___x_216_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
v___x_217_ = lean_usize_land(v_x_209_, v___x_216_);
v_j_218_ = lean_usize_to_nat(v___x_217_);
v___x_219_ = lean_array_get_size(v_es_213_);
v___x_220_ = lean_nat_dec_lt(v_j_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_dec(v_j_218_);
lean_dec(v_x_212_);
lean_dec_ref(v_x_211_);
return v_x_208_;
}
else
{
lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_257_; 
lean_inc_ref(v_es_213_);
v_isSharedCheck_257_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v_x_208_, 0);
lean_dec(v_unused_258_);
v___x_222_ = v_x_208_;
v_isShared_223_ = v_isSharedCheck_257_;
goto v_resetjp_221_;
}
else
{
lean_dec(v_x_208_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_257_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_v_224_; lean_object* v___x_225_; lean_object* v_xs_x27_226_; lean_object* v___y_228_; 
v_v_224_ = lean_array_fget(v_es_213_, v_j_218_);
v___x_225_ = lean_box(0);
v_xs_x27_226_ = lean_array_fset(v_es_213_, v_j_218_, v___x_225_);
switch(lean_obj_tag(v_v_224_))
{
case 0:
{
lean_object* v_key_233_; lean_object* v_val_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_244_; 
v_key_233_ = lean_ctor_get(v_v_224_, 0);
v_val_234_ = lean_ctor_get(v_v_224_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_v_224_);
if (v_isSharedCheck_244_ == 0)
{
v___x_236_ = v_v_224_;
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_val_234_);
lean_inc(v_key_233_);
lean_dec(v_v_224_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
uint8_t v___x_238_; 
v___x_238_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_211_, v_key_233_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_del_object(v___x_236_);
v___x_239_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_233_, v_val_234_, v_x_211_, v_x_212_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
v___y_228_ = v___x_240_;
goto v___jp_227_;
}
else
{
lean_object* v___x_242_; 
lean_dec(v_val_234_);
lean_dec(v_key_233_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v_x_212_);
lean_ctor_set(v___x_236_, 0, v_x_211_);
v___x_242_ = v___x_236_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_x_211_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_x_212_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
v___y_228_ = v___x_242_;
goto v___jp_227_;
}
}
}
}
case 1:
{
lean_object* v_node_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_255_; 
v_node_245_ = lean_ctor_get(v_v_224_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v_v_224_);
if (v_isSharedCheck_255_ == 0)
{
v___x_247_ = v_v_224_;
v_isShared_248_ = v_isSharedCheck_255_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_node_245_);
lean_dec(v_v_224_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_255_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_249_ = lean_usize_shift_right(v_x_209_, v___x_214_);
v___x_250_ = lean_usize_add(v_x_210_, v___x_215_);
v___x_251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_node_245_, v___x_249_, v___x_250_, v_x_211_, v_x_212_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_251_);
v___x_253_ = v___x_247_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
v___y_228_ = v___x_253_;
goto v___jp_227_;
}
}
}
default: 
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_x_211_);
lean_ctor_set(v___x_256_, 1, v_x_212_);
v___y_228_ = v___x_256_;
goto v___jp_227_;
}
}
v___jp_227_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = lean_array_fset(v_xs_x27_226_, v_j_218_, v___y_228_);
lean_dec(v_j_218_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_229_);
v___x_231_ = v___x_222_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
else
{
lean_object* v_ks_259_; lean_object* v_vs_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_280_; 
v_ks_259_ = lean_ctor_get(v_x_208_, 0);
v_vs_260_ = lean_ctor_get(v_x_208_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_280_ == 0)
{
v___x_262_ = v_x_208_;
v_isShared_263_ = v_isSharedCheck_280_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_vs_260_);
lean_inc(v_ks_259_);
lean_dec(v_x_208_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_280_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_ks_259_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_vs_260_);
v___x_265_ = v_reuseFailAlloc_279_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v_newNode_266_; uint8_t v___y_268_; size_t v___x_274_; uint8_t v___x_275_; 
v_newNode_266_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v___x_265_, v_x_211_, v_x_212_);
v___x_274_ = ((size_t)7ULL);
v___x_275_ = lean_usize_dec_le(v___x_274_, v_x_210_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_276_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_266_);
v___x_277_ = lean_unsigned_to_nat(4u);
v___x_278_ = lean_nat_dec_lt(v___x_276_, v___x_277_);
lean_dec(v___x_276_);
v___y_268_ = v___x_278_;
goto v___jp_267_;
}
else
{
v___y_268_ = v___x_275_;
goto v___jp_267_;
}
v___jp_267_:
{
if (v___y_268_ == 0)
{
lean_object* v_ks_269_; lean_object* v_vs_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_ks_269_ = lean_ctor_get(v_newNode_266_, 0);
lean_inc_ref(v_ks_269_);
v_vs_270_ = lean_ctor_get(v_newNode_266_, 1);
lean_inc_ref(v_vs_270_);
lean_dec_ref(v_newNode_266_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2);
v___x_273_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_x_210_, v_ks_269_, v_vs_270_, v___x_271_, v___x_272_);
lean_dec_ref(v_vs_270_);
lean_dec_ref(v_ks_269_);
return v___x_273_;
}
else
{
return v_newNode_266_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t v_depth_281_, lean_object* v_keys_282_, lean_object* v_vals_283_, lean_object* v_i_284_, lean_object* v_entries_285_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_array_get_size(v_keys_282_);
v___x_287_ = lean_nat_dec_lt(v_i_284_, v___x_286_);
if (v___x_287_ == 0)
{
lean_dec(v_i_284_);
return v_entries_285_;
}
else
{
lean_object* v_k_288_; lean_object* v_v_289_; uint64_t v___x_290_; size_t v_h_291_; size_t v___x_292_; lean_object* v___x_293_; size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v_h_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_k_288_ = lean_array_fget_borrowed(v_keys_282_, v_i_284_);
v_v_289_ = lean_array_fget_borrowed(v_vals_283_, v_i_284_);
v___x_290_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_288_);
v_h_291_ = lean_uint64_to_usize(v___x_290_);
v___x_292_ = ((size_t)5ULL);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = ((size_t)1ULL);
v___x_295_ = lean_usize_sub(v_depth_281_, v___x_294_);
v___x_296_ = lean_usize_mul(v___x_292_, v___x_295_);
v_h_297_ = lean_usize_shift_right(v_h_291_, v___x_296_);
v___x_298_ = lean_nat_add(v_i_284_, v___x_293_);
lean_dec(v_i_284_);
lean_inc(v_v_289_);
lean_inc(v_k_288_);
v___x_299_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_entries_285_, v_h_297_, v_depth_281_, v_k_288_, v_v_289_);
v_i_284_ = v___x_298_;
v_entries_285_ = v___x_299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_301_, lean_object* v_keys_302_, lean_object* v_vals_303_, lean_object* v_i_304_, lean_object* v_entries_305_){
_start:
{
size_t v_depth_boxed_306_; lean_object* v_res_307_; 
v_depth_boxed_306_ = lean_unbox_usize(v_depth_301_);
lean_dec(v_depth_301_);
v_res_307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_boxed_306_, v_keys_302_, v_vals_303_, v_i_304_, v_entries_305_);
lean_dec_ref(v_vals_303_);
lean_dec_ref(v_keys_302_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
size_t v_x_5199__boxed_313_; size_t v_x_5200__boxed_314_; lean_object* v_res_315_; 
v_x_5199__boxed_313_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_x_5200__boxed_314_ = lean_unbox_usize(v_x_310_);
lean_dec(v_x_310_);
v_res_315_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_308_, v_x_5199__boxed_313_, v_x_5200__boxed_314_, v_x_311_, v_x_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
uint64_t v___x_319_; size_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; 
v___x_319_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_317_);
v___x_320_ = lean_uint64_to_usize(v___x_319_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_316_, v___x_320_, v___x_321_, v_x_317_, v_x_318_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_323_, lean_object* v_vals_324_, lean_object* v_i_325_, lean_object* v_k_326_){
_start:
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_array_get_size(v_keys_323_);
v___x_328_ = lean_nat_dec_lt(v_i_325_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
lean_dec(v_i_325_);
v___x_329_ = lean_box(0);
return v___x_329_;
}
else
{
lean_object* v_k_x27_330_; uint8_t v___x_331_; 
v_k_x27_330_ = lean_array_fget_borrowed(v_keys_323_, v_i_325_);
v___x_331_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_326_, v_k_x27_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = lean_nat_add(v_i_325_, v___x_332_);
lean_dec(v_i_325_);
v_i_325_ = v___x_333_;
goto _start;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_array_fget_borrowed(v_vals_324_, v_i_325_);
lean_dec(v_i_325_);
lean_inc(v___x_335_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_337_, lean_object* v_vals_338_, lean_object* v_i_339_, lean_object* v_k_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_337_, v_vals_338_, v_i_339_, v_k_340_);
lean_dec_ref(v_k_340_);
lean_dec_ref(v_vals_338_);
lean_dec_ref(v_keys_337_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* v_x_342_, size_t v_x_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
lean_object* v_es_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_366_; 
v_es_345_ = lean_ctor_get(v_x_342_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_366_ == 0)
{
v___x_347_ = v_x_342_;
v_isShared_348_ = v_isSharedCheck_366_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_es_345_);
lean_dec(v_x_342_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_366_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; size_t v___x_350_; size_t v___x_351_; size_t v___x_352_; lean_object* v_j_353_; lean_object* v___x_354_; 
v___x_349_ = lean_box(2);
v___x_350_ = ((size_t)5ULL);
v___x_351_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
v___x_352_ = lean_usize_land(v_x_343_, v___x_351_);
v_j_353_ = lean_usize_to_nat(v___x_352_);
v___x_354_ = lean_array_get(v___x_349_, v_es_345_, v_j_353_);
lean_dec(v_j_353_);
lean_dec_ref(v_es_345_);
switch(lean_obj_tag(v___x_354_))
{
case 0:
{
lean_object* v_key_355_; lean_object* v_val_356_; uint8_t v___x_357_; 
v_key_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_key_355_);
v_val_356_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_val_356_);
lean_dec_ref(v___x_354_);
v___x_357_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_344_, v_key_355_);
lean_dec(v_key_355_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec(v_val_356_);
lean_del_object(v___x_347_);
v___x_358_ = lean_box(0);
return v___x_358_;
}
else
{
lean_object* v___x_360_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 1);
lean_ctor_set(v___x_347_, 0, v_val_356_);
v___x_360_ = v___x_347_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_val_356_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
case 1:
{
lean_object* v_node_362_; size_t v___x_363_; 
lean_del_object(v___x_347_);
v_node_362_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_node_362_);
lean_dec_ref(v___x_354_);
v___x_363_ = lean_usize_shift_right(v_x_343_, v___x_350_);
v_x_342_ = v_node_362_;
v_x_343_ = v___x_363_;
goto _start;
}
default: 
{
lean_object* v___x_365_; 
lean_del_object(v___x_347_);
v___x_365_ = lean_box(0);
return v___x_365_;
}
}
}
}
else
{
lean_object* v_ks_367_; lean_object* v_vs_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_ks_367_ = lean_ctor_get(v_x_342_, 0);
lean_inc_ref(v_ks_367_);
v_vs_368_ = lean_ctor_get(v_x_342_, 1);
lean_inc_ref(v_vs_368_);
lean_dec_ref(v_x_342_);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_ks_367_, v_vs_368_, v___x_369_, v_x_344_);
lean_dec_ref(v_vs_368_);
lean_dec_ref(v_ks_367_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_){
_start:
{
size_t v_x_5399__boxed_374_; lean_object* v_res_375_; 
v_x_5399__boxed_374_ = lean_unbox_usize(v_x_372_);
lean_dec(v_x_372_);
v_res_375_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_371_, v_x_5399__boxed_374_, v_x_373_);
lean_dec_ref(v_x_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
uint64_t v___x_378_; size_t v___x_379_; lean_object* v___x_380_; 
v___x_378_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_377_);
v___x_379_ = lean_uint64_to_usize(v___x_378_);
v___x_380_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_376_, v___x_379_, v_x_377_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_381_, v_x_382_);
lean_dec_ref(v_x_382_);
return v_res_383_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_387_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
v___x_388_ = lean_unsigned_to_nat(37u);
v___x_389_ = lean_unsigned_to_nat(52u);
v___x_390_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
v___x_391_ = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
v___x_392_ = l_mkPanicMessageWithDecl(v___x_391_, v___x_390_, v___x_389_, v___x_388_, v___x_387_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* v_e_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___y_402_; lean_object* v_a_432_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; uint8_t v___y_494_; lean_object* v_d_514_; lean_object* v_b_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_525_; 
switch(lean_obj_tag(v_e_393_))
{
case 1:
{
lean_object* v_fvarId_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_fvarId_554_ = lean_ctor_get(v_e_393_, 0);
lean_inc(v_fvarId_554_);
lean_dec_ref(v_e_393_);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v_fvarId_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
case 2:
{
lean_object* v_mvarId_557_; uint8_t v___y_559_; uint8_t v___x_600_; 
v_mvarId_557_ = lean_ctor_get(v_e_393_, 0);
v___x_600_ = l_Lean_Expr_hasFVar(v_e_393_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; 
v___x_601_ = l_Lean_Expr_hasMVar(v_e_393_);
v___y_559_ = v___x_601_;
goto v___jp_558_;
}
else
{
v___y_559_ = v___x_600_;
goto v___jp_558_;
}
v___jp_558_:
{
if (v___y_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec_ref(v_e_393_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v_maxFVar_563_; lean_object* v___x_564_; 
v___x_562_ = lean_st_ref_get(v_a_395_);
v_maxFVar_563_ = lean_ctor_get(v___x_562_, 1);
lean_inc_ref(v_maxFVar_563_);
lean_dec(v___x_562_);
v___x_564_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_563_, v_e_393_);
if (lean_obj_tag(v___x_564_) == 1)
{
lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec_ref(v_e_393_);
v_val_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 0);
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_val_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_object* v___x_573_; 
lean_dec(v___x_564_);
lean_inc(v_mvarId_557_);
v___x_573_ = l_Lean_MVarId_getDecl(v_mvarId_557_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_lctx_575_; lean_object* v_decls_576_; uint8_t v___x_577_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref(v___x_573_);
v_lctx_575_ = lean_ctor_get(v_a_574_, 1);
lean_inc_ref(v_lctx_575_);
lean_dec(v_a_574_);
v_decls_576_ = lean_ctor_get(v_lctx_575_, 1);
v___x_577_ = l_Lean_PersistentArray_isEmpty___redArg(v_decls_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_LocalContext_lastDecl(v_lctx_575_);
lean_dec_ref(v_lctx_575_);
if (lean_obj_tag(v___x_578_) == 1)
{
lean_object* v_val_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_587_; 
v_val_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_587_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_val_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = l_Lean_LocalDecl_fvarId(v_val_579_);
lean_dec(v_val_579_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_583_);
v___x_585_ = v___x_581_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
v_a_432_ = v___x_585_;
goto v___jp_431_;
}
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec(v___x_578_);
v___x_588_ = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
v___x_589_ = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(v___x_588_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref(v___x_589_);
v_a_432_ = v_a_590_;
goto v___jp_431_;
}
else
{
lean_dec_ref(v_e_393_);
return v___x_589_;
}
}
}
else
{
lean_object* v___x_591_; 
lean_dec_ref(v_lctx_575_);
v___x_591_ = lean_box(0);
v_a_432_ = v___x_591_;
goto v___jp_431_;
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v_e_393_);
v_a_592_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_573_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_573_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_602_; lean_object* v_arg_603_; uint8_t v___y_605_; uint8_t v___x_624_; 
v_fn_602_ = lean_ctor_get(v_e_393_, 0);
v_arg_603_ = lean_ctor_get(v_e_393_, 1);
v___x_624_ = l_Lean_Expr_hasFVar(v_e_393_);
if (v___x_624_ == 0)
{
uint8_t v___x_625_; 
v___x_625_ = l_Lean_Expr_hasMVar(v_e_393_);
v___y_605_ = v___x_625_;
goto v___jp_604_;
}
else
{
v___y_605_ = v___x_624_;
goto v___jp_604_;
}
v___jp_604_:
{
if (v___y_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec_ref(v_e_393_);
v___x_606_ = lean_box(0);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
else
{
lean_object* v___x_608_; lean_object* v_maxFVar_609_; lean_object* v___x_610_; 
v___x_608_ = lean_st_ref_get(v_a_395_);
v_maxFVar_609_ = lean_ctor_get(v___x_608_, 1);
lean_inc_ref(v_maxFVar_609_);
lean_dec(v___x_608_);
v___x_610_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_609_, v_e_393_);
if (lean_obj_tag(v___x_610_) == 1)
{
lean_object* v_val_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec_ref(v_e_393_);
v_val_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_val_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 0);
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_val_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
else
{
lean_object* v___x_619_; 
lean_dec(v___x_610_);
lean_inc_ref(v_fn_602_);
v___x_619_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_fn_602_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_621_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref(v___x_619_);
lean_inc_ref(v_arg_603_);
v___x_621_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_arg_603_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_623_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref(v___x_621_);
v___x_623_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_620_, v_a_622_, v_a_396_, v_a_398_, v_a_399_);
v___y_525_ = v___x_623_;
goto v___jp_524_;
}
else
{
lean_dec(v_a_620_);
v___y_525_ = v___x_621_;
goto v___jp_524_;
}
}
else
{
v___y_525_ = v___x_619_;
goto v___jp_524_;
}
}
}
}
}
case 6:
{
lean_object* v_binderType_626_; lean_object* v_body_627_; 
v_binderType_626_ = lean_ctor_get(v_e_393_, 1);
v_body_627_ = lean_ctor_get(v_e_393_, 2);
lean_inc_ref(v_body_627_);
lean_inc_ref(v_binderType_626_);
v_d_514_ = v_binderType_626_;
v_b_515_ = v_body_627_;
v___y_516_ = v_a_394_;
v___y_517_ = v_a_395_;
v___y_518_ = v_a_396_;
v___y_519_ = v_a_397_;
v___y_520_ = v_a_398_;
v___y_521_ = v_a_399_;
goto v___jp_513_;
}
case 7:
{
lean_object* v_binderType_628_; lean_object* v_body_629_; 
v_binderType_628_ = lean_ctor_get(v_e_393_, 1);
v_body_629_ = lean_ctor_get(v_e_393_, 2);
lean_inc_ref(v_body_629_);
lean_inc_ref(v_binderType_628_);
v_d_514_ = v_binderType_628_;
v_b_515_ = v_body_629_;
v___y_516_ = v_a_394_;
v___y_517_ = v_a_395_;
v___y_518_ = v_a_396_;
v___y_519_ = v_a_397_;
v___y_520_ = v_a_398_;
v___y_521_ = v_a_399_;
goto v___jp_513_;
}
case 8:
{
lean_object* v_type_630_; lean_object* v_value_631_; lean_object* v_body_632_; uint8_t v___y_634_; uint8_t v___x_657_; 
v_type_630_ = lean_ctor_get(v_e_393_, 1);
v_value_631_ = lean_ctor_get(v_e_393_, 2);
v_body_632_ = lean_ctor_get(v_e_393_, 3);
v___x_657_ = l_Lean_Expr_hasFVar(v_e_393_);
if (v___x_657_ == 0)
{
uint8_t v___x_658_; 
v___x_658_ = l_Lean_Expr_hasMVar(v_e_393_);
v___y_634_ = v___x_658_;
goto v___jp_633_;
}
else
{
v___y_634_ = v___x_657_;
goto v___jp_633_;
}
v___jp_633_:
{
if (v___y_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec_ref(v_e_393_);
v___x_635_ = lean_box(0);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; lean_object* v_maxFVar_638_; lean_object* v___x_639_; 
v___x_637_ = lean_st_ref_get(v_a_395_);
v_maxFVar_638_ = lean_ctor_get(v___x_637_, 1);
lean_inc_ref(v_maxFVar_638_);
lean_dec(v___x_637_);
v___x_639_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_638_, v_e_393_);
if (lean_obj_tag(v___x_639_) == 1)
{
lean_object* v_val_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_e_393_);
v_val_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_val_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 0);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_val_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v___x_648_; 
lean_dec(v___x_639_);
lean_inc_ref(v_type_630_);
v___x_648_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_type_630_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref(v___x_648_);
lean_inc_ref(v_value_631_);
v___x_650_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_value_631_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref(v___x_650_);
v___x_652_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_649_, v_a_651_, v_a_396_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref(v___x_652_);
lean_inc_ref(v_body_632_);
v___x_654_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_body_632_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref(v___x_654_);
v___x_656_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_653_, v_a_655_, v_a_396_, v_a_398_, v_a_399_);
v___y_402_ = v___x_656_;
goto v___jp_401_;
}
else
{
lean_dec(v_a_653_);
v___y_402_ = v___x_654_;
goto v___jp_401_;
}
}
else
{
v___y_402_ = v___x_652_;
goto v___jp_401_;
}
}
else
{
lean_dec(v_a_649_);
v___y_402_ = v___x_650_;
goto v___jp_401_;
}
}
else
{
v___y_402_ = v___x_648_;
goto v___jp_401_;
}
}
}
}
}
case 10:
{
lean_object* v_expr_659_; uint8_t v___y_661_; uint8_t v___x_704_; 
v_expr_659_ = lean_ctor_get(v_e_393_, 1);
lean_inc_ref(v_expr_659_);
lean_dec_ref(v_e_393_);
v___x_704_ = l_Lean_Expr_hasFVar(v_expr_659_);
if (v___x_704_ == 0)
{
uint8_t v___x_705_; 
v___x_705_ = l_Lean_Expr_hasMVar(v_expr_659_);
v___y_661_ = v___x_705_;
goto v___jp_660_;
}
else
{
v___y_661_ = v___x_704_;
goto v___jp_660_;
}
v___jp_660_:
{
if (v___y_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec_ref(v_expr_659_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v_maxFVar_665_; lean_object* v___x_666_; 
v___x_664_ = lean_st_ref_get(v_a_395_);
v_maxFVar_665_ = lean_ctor_get(v___x_664_, 1);
lean_inc_ref(v_maxFVar_665_);
lean_dec(v___x_664_);
v___x_666_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_665_, v_expr_659_);
if (lean_obj_tag(v___x_666_) == 1)
{
lean_object* v_val_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_expr_659_);
v_val_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_val_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 0);
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_val_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
else
{
lean_object* v___x_675_; 
lean_dec(v___x_666_);
lean_inc_ref(v_expr_659_);
v___x_675_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_expr_659_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_703_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_703_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_703_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_703_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v_share_681_; lean_object* v_maxFVar_682_; lean_object* v_proofInstInfo_683_; lean_object* v_inferType_684_; lean_object* v_getLevel_685_; lean_object* v_congrInfo_686_; lean_object* v_defEqI_687_; lean_object* v_extensions_688_; lean_object* v_issues_689_; uint8_t v_debug_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_702_; 
v___x_680_ = lean_st_ref_take(v_a_395_);
v_share_681_ = lean_ctor_get(v___x_680_, 0);
v_maxFVar_682_ = lean_ctor_get(v___x_680_, 1);
v_proofInstInfo_683_ = lean_ctor_get(v___x_680_, 2);
v_inferType_684_ = lean_ctor_get(v___x_680_, 3);
v_getLevel_685_ = lean_ctor_get(v___x_680_, 4);
v_congrInfo_686_ = lean_ctor_get(v___x_680_, 5);
v_defEqI_687_ = lean_ctor_get(v___x_680_, 6);
v_extensions_688_ = lean_ctor_get(v___x_680_, 7);
v_issues_689_ = lean_ctor_get(v___x_680_, 8);
v_debug_690_ = lean_ctor_get_uint8(v___x_680_, sizeof(void*)*9);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_702_ == 0)
{
v___x_692_ = v___x_680_;
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_issues_689_);
lean_inc(v_extensions_688_);
lean_inc(v_defEqI_687_);
lean_inc(v_congrInfo_686_);
lean_inc(v_getLevel_685_);
lean_inc(v_inferType_684_);
lean_inc(v_proofInstInfo_683_);
lean_inc(v_maxFVar_682_);
lean_inc(v_share_681_);
lean_dec(v___x_680_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
lean_inc(v_a_676_);
v___x_694_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_682_, v_expr_659_, v_a_676_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_share_681_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_proofInstInfo_683_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_inferType_684_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_getLevel_685_);
lean_ctor_set(v_reuseFailAlloc_701_, 5, v_congrInfo_686_);
lean_ctor_set(v_reuseFailAlloc_701_, 6, v_defEqI_687_);
lean_ctor_set(v_reuseFailAlloc_701_, 7, v_extensions_688_);
lean_ctor_set(v_reuseFailAlloc_701_, 8, v_issues_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*9, v_debug_690_);
v___x_696_ = v_reuseFailAlloc_701_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_st_ref_set(v_a_395_, v___x_696_);
if (v_isShared_679_ == 0)
{
v___x_699_ = v___x_678_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_676_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
else
{
lean_dec_ref(v_expr_659_);
return v___x_675_;
}
}
}
}
}
case 11:
{
lean_object* v_struct_706_; uint8_t v___y_708_; uint8_t v___x_751_; 
v_struct_706_ = lean_ctor_get(v_e_393_, 2);
v___x_751_ = l_Lean_Expr_hasFVar(v_e_393_);
if (v___x_751_ == 0)
{
uint8_t v___x_752_; 
v___x_752_ = l_Lean_Expr_hasMVar(v_e_393_);
v___y_708_ = v___x_752_;
goto v___jp_707_;
}
else
{
v___y_708_ = v___x_751_;
goto v___jp_707_;
}
v___jp_707_:
{
if (v___y_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref(v_e_393_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v_maxFVar_712_; lean_object* v___x_713_; 
v___x_711_ = lean_st_ref_get(v_a_395_);
v_maxFVar_712_ = lean_ctor_get(v___x_711_, 1);
lean_inc_ref(v_maxFVar_712_);
lean_dec(v___x_711_);
v___x_713_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_712_, v_e_393_);
if (lean_obj_tag(v___x_713_) == 1)
{
lean_object* v_val_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_e_393_);
v_val_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_val_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 0);
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_val_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v___x_722_; 
lean_dec(v___x_713_);
lean_inc_ref(v_struct_706_);
v___x_722_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_struct_706_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_750_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_750_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_750_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_750_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v_share_728_; lean_object* v_maxFVar_729_; lean_object* v_proofInstInfo_730_; lean_object* v_inferType_731_; lean_object* v_getLevel_732_; lean_object* v_congrInfo_733_; lean_object* v_defEqI_734_; lean_object* v_extensions_735_; lean_object* v_issues_736_; uint8_t v_debug_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_749_; 
v___x_727_ = lean_st_ref_take(v_a_395_);
v_share_728_ = lean_ctor_get(v___x_727_, 0);
v_maxFVar_729_ = lean_ctor_get(v___x_727_, 1);
v_proofInstInfo_730_ = lean_ctor_get(v___x_727_, 2);
v_inferType_731_ = lean_ctor_get(v___x_727_, 3);
v_getLevel_732_ = lean_ctor_get(v___x_727_, 4);
v_congrInfo_733_ = lean_ctor_get(v___x_727_, 5);
v_defEqI_734_ = lean_ctor_get(v___x_727_, 6);
v_extensions_735_ = lean_ctor_get(v___x_727_, 7);
v_issues_736_ = lean_ctor_get(v___x_727_, 8);
v_debug_737_ = lean_ctor_get_uint8(v___x_727_, sizeof(void*)*9);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_749_ == 0)
{
v___x_739_ = v___x_727_;
v_isShared_740_ = v_isSharedCheck_749_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_issues_736_);
lean_inc(v_extensions_735_);
lean_inc(v_defEqI_734_);
lean_inc(v_congrInfo_733_);
lean_inc(v_getLevel_732_);
lean_inc(v_inferType_731_);
lean_inc(v_proofInstInfo_730_);
lean_inc(v_maxFVar_729_);
lean_inc(v_share_728_);
lean_dec(v___x_727_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_749_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
lean_inc(v_a_723_);
v___x_741_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_729_, v_e_393_, v_a_723_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_share_728_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_proofInstInfo_730_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_inferType_731_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_getLevel_732_);
lean_ctor_set(v_reuseFailAlloc_748_, 5, v_congrInfo_733_);
lean_ctor_set(v_reuseFailAlloc_748_, 6, v_defEqI_734_);
lean_ctor_set(v_reuseFailAlloc_748_, 7, v_extensions_735_);
lean_ctor_set(v_reuseFailAlloc_748_, 8, v_issues_736_);
lean_ctor_set_uint8(v_reuseFailAlloc_748_, sizeof(void*)*9, v_debug_737_);
v___x_743_ = v_reuseFailAlloc_748_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = lean_st_ref_set(v_a_395_, v___x_743_);
if (v_isShared_726_ == 0)
{
v___x_746_ = v___x_725_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_723_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_393_);
return v___x_722_;
}
}
}
}
}
default: 
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v_e_393_);
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
v___jp_401_:
{
if (lean_obj_tag(v___y_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_430_; 
v_a_403_ = lean_ctor_get(v___y_402_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___y_402_);
if (v_isSharedCheck_430_ == 0)
{
v___x_405_ = v___y_402_;
v_isShared_406_ = v_isSharedCheck_430_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___y_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_430_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v_share_408_; lean_object* v_maxFVar_409_; lean_object* v_proofInstInfo_410_; lean_object* v_inferType_411_; lean_object* v_getLevel_412_; lean_object* v_congrInfo_413_; lean_object* v_defEqI_414_; lean_object* v_extensions_415_; lean_object* v_issues_416_; uint8_t v_debug_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_429_; 
v___x_407_ = lean_st_ref_take(v_a_395_);
v_share_408_ = lean_ctor_get(v___x_407_, 0);
v_maxFVar_409_ = lean_ctor_get(v___x_407_, 1);
v_proofInstInfo_410_ = lean_ctor_get(v___x_407_, 2);
v_inferType_411_ = lean_ctor_get(v___x_407_, 3);
v_getLevel_412_ = lean_ctor_get(v___x_407_, 4);
v_congrInfo_413_ = lean_ctor_get(v___x_407_, 5);
v_defEqI_414_ = lean_ctor_get(v___x_407_, 6);
v_extensions_415_ = lean_ctor_get(v___x_407_, 7);
v_issues_416_ = lean_ctor_get(v___x_407_, 8);
v_debug_417_ = lean_ctor_get_uint8(v___x_407_, sizeof(void*)*9);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_429_ == 0)
{
v___x_419_ = v___x_407_;
v_isShared_420_ = v_isSharedCheck_429_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_issues_416_);
lean_inc(v_extensions_415_);
lean_inc(v_defEqI_414_);
lean_inc(v_congrInfo_413_);
lean_inc(v_getLevel_412_);
lean_inc(v_inferType_411_);
lean_inc(v_proofInstInfo_410_);
lean_inc(v_maxFVar_409_);
lean_inc(v_share_408_);
lean_dec(v___x_407_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_429_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
lean_inc(v_a_403_);
v___x_421_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_409_, v_e_393_, v_a_403_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v___x_421_);
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_share_408_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_proofInstInfo_410_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_inferType_411_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_getLevel_412_);
lean_ctor_set(v_reuseFailAlloc_428_, 5, v_congrInfo_413_);
lean_ctor_set(v_reuseFailAlloc_428_, 6, v_defEqI_414_);
lean_ctor_set(v_reuseFailAlloc_428_, 7, v_extensions_415_);
lean_ctor_set(v_reuseFailAlloc_428_, 8, v_issues_416_);
lean_ctor_set_uint8(v_reuseFailAlloc_428_, sizeof(void*)*9, v_debug_417_);
v___x_423_ = v_reuseFailAlloc_428_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = lean_st_ref_set(v_a_395_, v___x_423_);
if (v_isShared_406_ == 0)
{
v___x_426_ = v___x_405_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_403_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_393_);
return v___y_402_;
}
}
v___jp_431_:
{
lean_object* v___x_433_; lean_object* v_share_434_; lean_object* v_maxFVar_435_; lean_object* v_proofInstInfo_436_; lean_object* v_inferType_437_; lean_object* v_getLevel_438_; lean_object* v_congrInfo_439_; lean_object* v_defEqI_440_; lean_object* v_extensions_441_; lean_object* v_issues_442_; uint8_t v_debug_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_453_; 
v___x_433_ = lean_st_ref_take(v_a_395_);
v_share_434_ = lean_ctor_get(v___x_433_, 0);
v_maxFVar_435_ = lean_ctor_get(v___x_433_, 1);
v_proofInstInfo_436_ = lean_ctor_get(v___x_433_, 2);
v_inferType_437_ = lean_ctor_get(v___x_433_, 3);
v_getLevel_438_ = lean_ctor_get(v___x_433_, 4);
v_congrInfo_439_ = lean_ctor_get(v___x_433_, 5);
v_defEqI_440_ = lean_ctor_get(v___x_433_, 6);
v_extensions_441_ = lean_ctor_get(v___x_433_, 7);
v_issues_442_ = lean_ctor_get(v___x_433_, 8);
v_debug_443_ = lean_ctor_get_uint8(v___x_433_, sizeof(void*)*9);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_453_ == 0)
{
v___x_445_ = v___x_433_;
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_issues_442_);
lean_inc(v_extensions_441_);
lean_inc(v_defEqI_440_);
lean_inc(v_congrInfo_439_);
lean_inc(v_getLevel_438_);
lean_inc(v_inferType_437_);
lean_inc(v_proofInstInfo_436_);
lean_inc(v_maxFVar_435_);
lean_inc(v_share_434_);
lean_dec(v___x_433_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
lean_inc(v_a_432_);
v___x_447_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_435_, v_e_393_, v_a_432_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_447_);
v___x_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_share_434_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_proofInstInfo_436_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_inferType_437_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_getLevel_438_);
lean_ctor_set(v_reuseFailAlloc_452_, 5, v_congrInfo_439_);
lean_ctor_set(v_reuseFailAlloc_452_, 6, v_defEqI_440_);
lean_ctor_set(v_reuseFailAlloc_452_, 7, v_extensions_441_);
lean_ctor_set(v_reuseFailAlloc_452_, 8, v_issues_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_452_, sizeof(void*)*9, v_debug_443_);
v___x_449_ = v_reuseFailAlloc_452_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_st_ref_set(v_a_395_, v___x_449_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v_a_432_);
return v___x_451_;
}
}
}
v___jp_454_:
{
if (lean_obj_tag(v___y_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_484_; 
v_a_457_ = lean_ctor_get(v___y_456_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___y_456_);
if (v_isSharedCheck_484_ == 0)
{
v___x_459_ = v___y_456_;
v_isShared_460_ = v_isSharedCheck_484_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___y_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_484_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v_share_462_; lean_object* v_maxFVar_463_; lean_object* v_proofInstInfo_464_; lean_object* v_inferType_465_; lean_object* v_getLevel_466_; lean_object* v_congrInfo_467_; lean_object* v_defEqI_468_; lean_object* v_extensions_469_; lean_object* v_issues_470_; uint8_t v_debug_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_483_; 
v___x_461_ = lean_st_ref_take(v___y_455_);
v_share_462_ = lean_ctor_get(v___x_461_, 0);
v_maxFVar_463_ = lean_ctor_get(v___x_461_, 1);
v_proofInstInfo_464_ = lean_ctor_get(v___x_461_, 2);
v_inferType_465_ = lean_ctor_get(v___x_461_, 3);
v_getLevel_466_ = lean_ctor_get(v___x_461_, 4);
v_congrInfo_467_ = lean_ctor_get(v___x_461_, 5);
v_defEqI_468_ = lean_ctor_get(v___x_461_, 6);
v_extensions_469_ = lean_ctor_get(v___x_461_, 7);
v_issues_470_ = lean_ctor_get(v___x_461_, 8);
v_debug_471_ = lean_ctor_get_uint8(v___x_461_, sizeof(void*)*9);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_483_ == 0)
{
v___x_473_ = v___x_461_;
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_issues_470_);
lean_inc(v_extensions_469_);
lean_inc(v_defEqI_468_);
lean_inc(v_congrInfo_467_);
lean_inc(v_getLevel_466_);
lean_inc(v_inferType_465_);
lean_inc(v_proofInstInfo_464_);
lean_inc(v_maxFVar_463_);
lean_inc(v_share_462_);
lean_dec(v___x_461_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_477_; 
lean_inc(v_a_457_);
v___x_475_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_463_, v_e_393_, v_a_457_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_475_);
v___x_477_ = v___x_473_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_share_462_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_proofInstInfo_464_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_inferType_465_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_getLevel_466_);
lean_ctor_set(v_reuseFailAlloc_482_, 5, v_congrInfo_467_);
lean_ctor_set(v_reuseFailAlloc_482_, 6, v_defEqI_468_);
lean_ctor_set(v_reuseFailAlloc_482_, 7, v_extensions_469_);
lean_ctor_set(v_reuseFailAlloc_482_, 8, v_issues_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*9, v_debug_471_);
v___x_477_ = v_reuseFailAlloc_482_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = lean_st_ref_set(v___y_455_, v___x_477_);
if (v_isShared_460_ == 0)
{
v___x_480_ = v___x_459_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_457_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_393_);
return v___y_456_;
}
}
v___jp_485_:
{
if (v___y_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec_ref(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec_ref(v_e_393_);
v___x_495_ = lean_box(0);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; lean_object* v_maxFVar_498_; lean_object* v___x_499_; 
v___x_497_ = lean_st_ref_get(v___y_490_);
v_maxFVar_498_ = lean_ctor_get(v___x_497_, 1);
lean_inc_ref(v_maxFVar_498_);
lean_dec(v___x_497_);
v___x_499_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_maxFVar_498_, v_e_393_);
if (lean_obj_tag(v___x_499_) == 1)
{
lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec_ref(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec_ref(v_e_393_);
v_val_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 0);
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_val_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
else
{
lean_object* v___x_508_; 
lean_dec(v___x_499_);
v___x_508_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_487_, v___y_489_, v___y_490_, v___y_491_, v___y_486_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
v___x_510_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_486_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(v_a_509_, v_a_511_, v___y_491_, v___y_492_, v___y_493_);
v___y_455_ = v___y_490_;
v___y_456_ = v___x_512_;
goto v___jp_454_;
}
else
{
lean_dec(v_a_509_);
v___y_455_ = v___y_490_;
v___y_456_ = v___x_510_;
goto v___jp_454_;
}
}
else
{
lean_dec_ref(v___y_488_);
v___y_455_ = v___y_490_;
v___y_456_ = v___x_508_;
goto v___jp_454_;
}
}
}
}
v___jp_513_:
{
uint8_t v___x_522_; 
v___x_522_ = l_Lean_Expr_hasFVar(v_e_393_);
if (v___x_522_ == 0)
{
uint8_t v___x_523_; 
v___x_523_ = l_Lean_Expr_hasMVar(v_e_393_);
v___y_486_ = v___y_519_;
v___y_487_ = v_d_514_;
v___y_488_ = v_b_515_;
v___y_489_ = v___y_516_;
v___y_490_ = v___y_517_;
v___y_491_ = v___y_518_;
v___y_492_ = v___y_520_;
v___y_493_ = v___y_521_;
v___y_494_ = v___x_523_;
goto v___jp_485_;
}
else
{
v___y_486_ = v___y_519_;
v___y_487_ = v_d_514_;
v___y_488_ = v_b_515_;
v___y_489_ = v___y_516_;
v___y_490_ = v___y_517_;
v___y_491_ = v___y_518_;
v___y_492_ = v___y_520_;
v___y_493_ = v___y_521_;
v___y_494_ = v___x_522_;
goto v___jp_485_;
}
}
v___jp_524_:
{
if (lean_obj_tag(v___y_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_553_; 
v_a_526_ = lean_ctor_get(v___y_525_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___y_525_);
if (v_isSharedCheck_553_ == 0)
{
v___x_528_ = v___y_525_;
v_isShared_529_ = v_isSharedCheck_553_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___y_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_553_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v_share_531_; lean_object* v_maxFVar_532_; lean_object* v_proofInstInfo_533_; lean_object* v_inferType_534_; lean_object* v_getLevel_535_; lean_object* v_congrInfo_536_; lean_object* v_defEqI_537_; lean_object* v_extensions_538_; lean_object* v_issues_539_; uint8_t v_debug_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_552_; 
v___x_530_ = lean_st_ref_take(v_a_395_);
v_share_531_ = lean_ctor_get(v___x_530_, 0);
v_maxFVar_532_ = lean_ctor_get(v___x_530_, 1);
v_proofInstInfo_533_ = lean_ctor_get(v___x_530_, 2);
v_inferType_534_ = lean_ctor_get(v___x_530_, 3);
v_getLevel_535_ = lean_ctor_get(v___x_530_, 4);
v_congrInfo_536_ = lean_ctor_get(v___x_530_, 5);
v_defEqI_537_ = lean_ctor_get(v___x_530_, 6);
v_extensions_538_ = lean_ctor_get(v___x_530_, 7);
v_issues_539_ = lean_ctor_get(v___x_530_, 8);
v_debug_540_ = lean_ctor_get_uint8(v___x_530_, sizeof(void*)*9);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_552_ == 0)
{
v___x_542_ = v___x_530_;
v_isShared_543_ = v_isSharedCheck_552_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_issues_539_);
lean_inc(v_extensions_538_);
lean_inc(v_defEqI_537_);
lean_inc(v_congrInfo_536_);
lean_inc(v_getLevel_535_);
lean_inc(v_inferType_534_);
lean_inc(v_proofInstInfo_533_);
lean_inc(v_maxFVar_532_);
lean_inc(v_share_531_);
lean_dec(v___x_530_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_552_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
lean_inc(v_a_526_);
v___x_544_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_maxFVar_532_, v_e_393_, v_a_526_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_share_531_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_proofInstInfo_533_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_inferType_534_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v_getLevel_535_);
lean_ctor_set(v_reuseFailAlloc_551_, 5, v_congrInfo_536_);
lean_ctor_set(v_reuseFailAlloc_551_, 6, v_defEqI_537_);
lean_ctor_set(v_reuseFailAlloc_551_, 7, v_extensions_538_);
lean_ctor_set(v_reuseFailAlloc_551_, 8, v_issues_539_);
lean_ctor_set_uint8(v_reuseFailAlloc_551_, sizeof(void*)*9, v_debug_540_);
v___x_546_ = v_reuseFailAlloc_551_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_st_ref_set(v_a_395_, v___x_546_);
if (v_isShared_529_ == 0)
{
v___x_549_ = v___x_528_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_526_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_393_);
return v___y_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* v_e_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_e_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* v_00_u03b2_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(v_x_765_, v_x_766_, v_x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* v_00_u03b2_769_, lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(v_x_770_, v_x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* v_00_u03b2_773_, lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(v_00_u03b2_773_, v_x_774_, v_x_775_);
lean_dec_ref(v_x_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* v_00_u03b2_777_, lean_object* v_x_778_, size_t v_x_779_, size_t v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(v_x_778_, v_x_779_, v_x_780_, v_x_781_, v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_784_, lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
size_t v_x_6109__boxed_790_; size_t v_x_6110__boxed_791_; lean_object* v_res_792_; 
v_x_6109__boxed_790_ = lean_unbox_usize(v_x_786_);
lean_dec(v_x_786_);
v_x_6110__boxed_791_ = lean_unbox_usize(v_x_787_);
lean_dec(v_x_787_);
v_res_792_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(v_00_u03b2_784_, v_x_785_, v_x_6109__boxed_790_, v_x_6110__boxed_791_, v_x_788_, v_x_789_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, size_t v_x_795_, lean_object* v_x_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(v_x_794_, v_x_795_, v_x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_798_, lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
size_t v_x_6126__boxed_802_; lean_object* v_res_803_; 
v_x_6126__boxed_802_ = lean_unbox_usize(v_x_800_);
lean_dec(v_x_800_);
v_res_803_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(v_00_u03b2_798_, v_x_799_, v_x_6126__boxed_802_, v_x_801_);
lean_dec_ref(v_x_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_804_, lean_object* v_n_805_, lean_object* v_k_806_, lean_object* v_v_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(v_n_805_, v_k_806_, v_v_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_809_, size_t v_depth_810_, lean_object* v_keys_811_, lean_object* v_vals_812_, lean_object* v_heq_813_, lean_object* v_i_814_, lean_object* v_entries_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(v_depth_810_, v_keys_811_, v_vals_812_, v_i_814_, v_entries_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_817_, lean_object* v_depth_818_, lean_object* v_keys_819_, lean_object* v_vals_820_, lean_object* v_heq_821_, lean_object* v_i_822_, lean_object* v_entries_823_){
_start:
{
size_t v_depth_boxed_824_; lean_object* v_res_825_; 
v_depth_boxed_824_ = lean_unbox_usize(v_depth_818_);
lean_dec(v_depth_818_);
v_res_825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(v_00_u03b2_817_, v_depth_boxed_824_, v_keys_819_, v_vals_820_, v_heq_821_, v_i_822_, v_entries_823_);
lean_dec_ref(v_vals_820_);
lean_dec_ref(v_keys_819_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_826_, lean_object* v_keys_827_, lean_object* v_vals_828_, lean_object* v_heq_829_, lean_object* v_i_830_, lean_object* v_k_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(v_keys_827_, v_vals_828_, v_i_830_, v_k_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_833_, lean_object* v_keys_834_, lean_object* v_vals_835_, lean_object* v_heq_836_, lean_object* v_i_837_, lean_object* v_k_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(v_00_u03b2_833_, v_keys_834_, v_vals_835_, v_heq_836_, v_i_837_, v_k_838_);
lean_dec_ref(v_k_838_);
lean_dec_ref(v_vals_835_);
lean_dec_ref(v_keys_834_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_841_, v_x_842_, v_x_843_, v_x_844_);
return v___x_845_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_MaxFVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_MaxFVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_MaxFVar(builtin);
}
#ifdef __cplusplus
}
#endif
