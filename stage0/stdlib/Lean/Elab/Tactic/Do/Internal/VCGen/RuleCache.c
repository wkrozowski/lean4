// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache
// Imports: public import Lean.Elab.Tactic.Do.VCGen.Split public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction public import Lean.Elab.Tactic.Do.Internal.VCGen.Util import Lean.Meta.Sym.InferType
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
lean_object* lean_st_ref_get(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeSplit_mkBackwardRuleForLattice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tryMkBackwardRuleFromSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_14_ = lean_apply_12(v_k_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0___boxed(lean_object* v_k_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(v_k_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(lean_object* v_k_29_, uint8_t v_allowLevelAssignments_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; 
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
lean_inc(v___y_32_);
lean_inc_ref(v___y_31_);
v___f_43_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_43_, 0, v_k_29_);
lean_closure_set(v___f_43_, 1, v___y_31_);
lean_closure_set(v___f_43_, 2, v___y_32_);
lean_closure_set(v___f_43_, 3, v___y_33_);
lean_closure_set(v___f_43_, 4, v___y_34_);
lean_closure_set(v___f_43_, 5, v___y_35_);
lean_closure_set(v___f_43_, 6, v___y_36_);
lean_closure_set(v___f_43_, 7, v___y_37_);
v___x_44_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_30_, v___f_43_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
if (lean_obj_tag(v___x_44_) == 0)
{
return v___x_44_;
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___boxed(lean_object* v_k_53_, lean_object* v_allowLevelAssignments_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_67_; lean_object* v_res_68_; 
v_allowLevelAssignments_boxed_67_ = lean_unbox(v_allowLevelAssignments_54_);
v_res_68_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_k_53_, v_allowLevelAssignments_boxed_67_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(lean_object* v_00_u03b1_69_, lean_object* v_k_70_, uint8_t v_allowLevelAssignments_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_k_70_, v_allowLevelAssignments_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___boxed(lean_object* v_00_u03b1_85_, lean_object* v_k_86_, lean_object* v_allowLevelAssignments_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_100_; lean_object* v_res_101_; 
v_allowLevelAssignments_boxed_100_ = lean_unbox(v_allowLevelAssignments_87_);
v_res_101_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(v_00_u03b1_85_, v_k_86_, v_allowLevelAssignments_boxed_100_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(lean_object* v_specThm_102_, lean_object* v_info_103_, lean_object* v___x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tryMkBackwardRuleFromSpec(v_specThm_102_, v_info_103_, v___x_104_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_126_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_122_, 0, v_a_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
v_a_127_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_117_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_117_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed(lean_object* v_specThm_135_, lean_object* v_info_136_, lean_object* v___x_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(v_specThm_135_, v_info_136_, v___x_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec_ref(v_info_136_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object* v_a_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v___x_153_; 
v___x_153_ = lean_box(0);
return v___x_153_;
}
else
{
lean_object* v_key_154_; lean_object* v_value_155_; lean_object* v_tail_156_; uint8_t v___y_158_; lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v_fst_163_; lean_object* v_snd_164_; uint8_t v___x_165_; 
v_key_154_ = lean_ctor_get(v_x_152_, 0);
v_value_155_ = lean_ctor_get(v_x_152_, 1);
v_tail_156_ = lean_ctor_get(v_x_152_, 2);
v_fst_161_ = lean_ctor_get(v_key_154_, 0);
v_snd_162_ = lean_ctor_get(v_key_154_, 1);
v_fst_163_ = lean_ctor_get(v_a_151_, 0);
v_snd_164_ = lean_ctor_get(v_a_151_, 1);
v___x_165_ = lean_name_eq(v_fst_161_, v_fst_163_);
if (v___x_165_ == 0)
{
v___y_158_ = v___x_165_;
goto v___jp_157_;
}
else
{
lean_object* v_fst_166_; lean_object* v_snd_167_; lean_object* v_fst_168_; lean_object* v_snd_169_; uint8_t v___x_170_; 
v_fst_166_ = lean_ctor_get(v_snd_162_, 0);
v_snd_167_ = lean_ctor_get(v_snd_162_, 1);
v_fst_168_ = lean_ctor_get(v_snd_164_, 0);
v_snd_169_ = lean_ctor_get(v_snd_164_, 1);
v___x_170_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_166_, v_fst_168_);
if (v___x_170_ == 0)
{
v___y_158_ = v___x_170_;
goto v___jp_157_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_eq(v_snd_167_, v_snd_169_);
v___y_158_ = v___x_171_;
goto v___jp_157_;
}
}
v___jp_157_:
{
if (v___y_158_ == 0)
{
v_x_152_ = v_tail_156_;
goto _start;
}
else
{
lean_object* v___x_160_; 
lean_inc(v_value_155_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v_value_155_);
return v___x_160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_172_, lean_object* v_x_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_172_, v_x_173_);
lean_dec(v_x_173_);
lean_dec_ref(v_a_172_);
return v_res_174_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_175_; uint64_t v___x_176_; 
v___x_175_ = lean_unsigned_to_nat(1723u);
v___x_176_ = lean_uint64_of_nat(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object* v_m_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_buckets_179_; lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_182_; uint64_t v___y_184_; 
v_buckets_179_ = lean_ctor_get(v_m_177_, 1);
v_fst_180_ = lean_ctor_get(v_a_178_, 0);
v_snd_181_ = lean_ctor_get(v_a_178_, 1);
v___x_182_ = lean_array_get_size(v_buckets_179_);
if (lean_obj_tag(v_fst_180_) == 0)
{
uint64_t v___x_204_; 
v___x_204_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_184_ = v___x_204_;
goto v___jp_183_;
}
else
{
uint64_t v_hash_205_; 
v_hash_205_ = lean_ctor_get_uint64(v_fst_180_, sizeof(void*)*2);
v___y_184_ = v_hash_205_;
goto v___jp_183_;
}
v___jp_183_:
{
lean_object* v_fst_185_; lean_object* v_snd_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v_fold_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_fst_185_ = lean_ctor_get(v_snd_181_, 0);
v_snd_186_ = lean_ctor_get(v_snd_181_, 1);
v___x_187_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_185_);
v___x_188_ = lean_uint64_of_nat(v_snd_186_);
v___x_189_ = lean_uint64_mix_hash(v___x_187_, v___x_188_);
v___x_190_ = lean_uint64_mix_hash(v___y_184_, v___x_189_);
v___x_191_ = 32ULL;
v___x_192_ = lean_uint64_shift_right(v___x_190_, v___x_191_);
v_fold_193_ = lean_uint64_xor(v___x_190_, v___x_192_);
v___x_194_ = 16ULL;
v___x_195_ = lean_uint64_shift_right(v_fold_193_, v___x_194_);
v___x_196_ = lean_uint64_xor(v_fold_193_, v___x_195_);
v___x_197_ = lean_uint64_to_usize(v___x_196_);
v___x_198_ = lean_usize_of_nat(v___x_182_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_sub(v___x_198_, v___x_199_);
v___x_201_ = lean_usize_land(v___x_197_, v___x_200_);
v___x_202_ = lean_array_uget_borrowed(v_buckets_179_, v___x_201_);
v___x_203_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_178_, v___x_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object* v_m_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_206_, v_a_207_);
lean_dec_ref(v_a_207_);
lean_dec_ref(v_m_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
return v_x_209_;
}
else
{
lean_object* v_key_211_; lean_object* v_value_212_; lean_object* v_tail_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_247_; 
v_key_211_ = lean_ctor_get(v_x_210_, 0);
v_value_212_ = lean_ctor_get(v_x_210_, 1);
v_tail_213_ = lean_ctor_get(v_x_210_, 2);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_247_ == 0)
{
v___x_215_ = v_x_210_;
v_isShared_216_ = v_isSharedCheck_247_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_tail_213_);
lean_inc(v_value_212_);
lean_inc(v_key_211_);
lean_dec(v_x_210_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_247_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___x_219_; uint64_t v___y_221_; 
v_fst_217_ = lean_ctor_get(v_key_211_, 0);
v_snd_218_ = lean_ctor_get(v_key_211_, 1);
v___x_219_ = lean_array_get_size(v_x_209_);
if (lean_obj_tag(v_fst_217_) == 0)
{
uint64_t v___x_245_; 
v___x_245_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_221_ = v___x_245_;
goto v___jp_220_;
}
else
{
uint64_t v_hash_246_; 
v_hash_246_ = lean_ctor_get_uint64(v_fst_217_, sizeof(void*)*2);
v___y_221_ = v_hash_246_;
goto v___jp_220_;
}
v___jp_220_:
{
lean_object* v_fst_222_; lean_object* v_snd_223_; uint64_t v___x_224_; uint64_t v___x_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v_fold_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v_fst_222_ = lean_ctor_get(v_snd_218_, 0);
v_snd_223_ = lean_ctor_get(v_snd_218_, 1);
v___x_224_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_222_);
v___x_225_ = lean_uint64_of_nat(v_snd_223_);
v___x_226_ = lean_uint64_mix_hash(v___x_224_, v___x_225_);
v___x_227_ = lean_uint64_mix_hash(v___y_221_, v___x_226_);
v___x_228_ = 32ULL;
v___x_229_ = lean_uint64_shift_right(v___x_227_, v___x_228_);
v_fold_230_ = lean_uint64_xor(v___x_227_, v___x_229_);
v___x_231_ = 16ULL;
v___x_232_ = lean_uint64_shift_right(v_fold_230_, v___x_231_);
v___x_233_ = lean_uint64_xor(v_fold_230_, v___x_232_);
v___x_234_ = lean_uint64_to_usize(v___x_233_);
v___x_235_ = lean_usize_of_nat(v___x_219_);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_sub(v___x_235_, v___x_236_);
v___x_238_ = lean_usize_land(v___x_234_, v___x_237_);
v___x_239_ = lean_array_uget_borrowed(v_x_209_, v___x_238_);
lean_inc(v___x_239_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 2, v___x_239_);
v___x_241_ = v___x_215_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_key_211_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_value_212_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v___x_239_);
v___x_241_ = v_reuseFailAlloc_244_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = lean_array_uset(v_x_209_, v___x_238_, v___x_241_);
v_x_209_ = v___x_242_;
v_x_210_ = v_tail_213_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(lean_object* v_i_248_, lean_object* v_source_249_, lean_object* v_target_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_array_get_size(v_source_249_);
v___x_252_ = lean_nat_dec_lt(v_i_248_, v___x_251_);
if (v___x_252_ == 0)
{
lean_dec_ref(v_source_249_);
lean_dec(v_i_248_);
return v_target_250_;
}
else
{
lean_object* v_es_253_; lean_object* v___x_254_; lean_object* v_source_255_; lean_object* v_target_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_es_253_ = lean_array_fget(v_source_249_, v_i_248_);
v___x_254_ = lean_box(0);
v_source_255_ = lean_array_fset(v_source_249_, v_i_248_, v___x_254_);
v_target_256_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_target_250_, v_es_253_);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_i_248_, v___x_257_);
lean_dec(v_i_248_);
v_i_248_ = v___x_258_;
v_source_249_ = v_source_255_;
v_target_250_ = v_target_256_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(lean_object* v_data_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_nbuckets_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_261_ = lean_array_get_size(v_data_260_);
v___x_262_ = lean_unsigned_to_nat(2u);
v_nbuckets_263_ = lean_nat_mul(v___x_261_, v___x_262_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_box(0);
v___x_266_ = lean_mk_array(v_nbuckets_263_, v___x_265_);
v___x_267_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v___x_264_, v_data_260_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(lean_object* v_a_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
uint8_t v___x_270_; 
v___x_270_ = 0;
return v___x_270_;
}
else
{
lean_object* v_key_271_; lean_object* v_tail_272_; uint8_t v___y_274_; lean_object* v_fst_276_; lean_object* v_snd_277_; lean_object* v_fst_278_; lean_object* v_snd_279_; uint8_t v___x_280_; 
v_key_271_ = lean_ctor_get(v_x_269_, 0);
v_tail_272_ = lean_ctor_get(v_x_269_, 2);
v_fst_276_ = lean_ctor_get(v_key_271_, 0);
v_snd_277_ = lean_ctor_get(v_key_271_, 1);
v_fst_278_ = lean_ctor_get(v_a_268_, 0);
v_snd_279_ = lean_ctor_get(v_a_268_, 1);
v___x_280_ = lean_name_eq(v_fst_276_, v_fst_278_);
if (v___x_280_ == 0)
{
v___y_274_ = v___x_280_;
goto v___jp_273_;
}
else
{
lean_object* v_fst_281_; lean_object* v_snd_282_; lean_object* v_fst_283_; lean_object* v_snd_284_; uint8_t v___x_285_; 
v_fst_281_ = lean_ctor_get(v_snd_277_, 0);
v_snd_282_ = lean_ctor_get(v_snd_277_, 1);
v_fst_283_ = lean_ctor_get(v_snd_279_, 0);
v_snd_284_ = lean_ctor_get(v_snd_279_, 1);
v___x_285_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_281_, v_fst_283_);
if (v___x_285_ == 0)
{
v___y_274_ = v___x_285_;
goto v___jp_273_;
}
else
{
uint8_t v___x_286_; 
v___x_286_ = lean_nat_dec_eq(v_snd_282_, v_snd_284_);
v___y_274_ = v___x_286_;
goto v___jp_273_;
}
}
v___jp_273_:
{
if (v___y_274_ == 0)
{
v_x_269_ = v_tail_272_;
goto _start;
}
else
{
return v___y_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object* v_a_287_, lean_object* v_x_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_287_, v_x_288_);
lean_dec(v_x_288_);
lean_dec_ref(v_a_287_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(lean_object* v_a_291_, lean_object* v_b_292_, lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_dec(v_b_292_);
lean_dec_ref(v_a_291_);
return v_x_293_;
}
else
{
lean_object* v_key_294_; lean_object* v_value_295_; lean_object* v_tail_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_320_; 
v_key_294_ = lean_ctor_get(v_x_293_, 0);
v_value_295_ = lean_ctor_get(v_x_293_, 1);
v_tail_296_ = lean_ctor_get(v_x_293_, 2);
v_isSharedCheck_320_ = !lean_is_exclusive(v_x_293_);
if (v_isSharedCheck_320_ == 0)
{
v___x_298_ = v_x_293_;
v_isShared_299_ = v_isSharedCheck_320_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_tail_296_);
lean_inc(v_value_295_);
lean_inc(v_key_294_);
lean_dec(v_x_293_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_320_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
uint8_t v___y_301_; lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v_fst_311_; lean_object* v_snd_312_; uint8_t v___x_313_; 
v_fst_309_ = lean_ctor_get(v_key_294_, 0);
v_snd_310_ = lean_ctor_get(v_key_294_, 1);
v_fst_311_ = lean_ctor_get(v_a_291_, 0);
v_snd_312_ = lean_ctor_get(v_a_291_, 1);
v___x_313_ = lean_name_eq(v_fst_309_, v_fst_311_);
if (v___x_313_ == 0)
{
v___y_301_ = v___x_313_;
goto v___jp_300_;
}
else
{
lean_object* v_fst_314_; lean_object* v_snd_315_; lean_object* v_fst_316_; lean_object* v_snd_317_; uint8_t v___x_318_; 
v_fst_314_ = lean_ctor_get(v_snd_310_, 0);
v_snd_315_ = lean_ctor_get(v_snd_310_, 1);
v_fst_316_ = lean_ctor_get(v_snd_312_, 0);
v_snd_317_ = lean_ctor_get(v_snd_312_, 1);
v___x_318_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_314_, v_fst_316_);
if (v___x_318_ == 0)
{
v___y_301_ = v___x_318_;
goto v___jp_300_;
}
else
{
uint8_t v___x_319_; 
v___x_319_ = lean_nat_dec_eq(v_snd_315_, v_snd_317_);
v___y_301_ = v___x_319_;
goto v___jp_300_;
}
}
v___jp_300_:
{
if (v___y_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_291_, v_b_292_, v_tail_296_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 2, v___x_302_);
v___x_304_ = v___x_298_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_key_294_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_value_295_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
else
{
lean_object* v___x_307_; 
lean_dec(v_value_295_);
lean_dec(v_key_294_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v_b_292_);
lean_ctor_set(v___x_298_, 0, v_a_291_);
v___x_307_ = v___x_298_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_291_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_b_292_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_tail_296_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object* v_m_321_, lean_object* v_a_322_, lean_object* v_b_323_){
_start:
{
lean_object* v_size_324_; lean_object* v_buckets_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_379_; 
v_size_324_ = lean_ctor_get(v_m_321_, 0);
v_buckets_325_ = lean_ctor_get(v_m_321_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_m_321_);
if (v_isSharedCheck_379_ == 0)
{
v___x_327_ = v_m_321_;
v_isShared_328_ = v_isSharedCheck_379_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_buckets_325_);
lean_inc(v_size_324_);
lean_dec(v_m_321_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_379_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_fst_329_; lean_object* v_snd_330_; lean_object* v___x_331_; uint64_t v___y_333_; 
v_fst_329_ = lean_ctor_get(v_a_322_, 0);
v_snd_330_ = lean_ctor_get(v_a_322_, 1);
v___x_331_ = lean_array_get_size(v_buckets_325_);
if (lean_obj_tag(v_fst_329_) == 0)
{
uint64_t v___x_377_; 
v___x_377_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_333_ = v___x_377_;
goto v___jp_332_;
}
else
{
uint64_t v_hash_378_; 
v_hash_378_ = lean_ctor_get_uint64(v_fst_329_, sizeof(void*)*2);
v___y_333_ = v_hash_378_;
goto v___jp_332_;
}
v___jp_332_:
{
lean_object* v_fst_334_; lean_object* v_snd_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v_fold_342_; uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; lean_object* v_bkt_351_; uint8_t v___x_352_; 
v_fst_334_ = lean_ctor_get(v_snd_330_, 0);
v_snd_335_ = lean_ctor_get(v_snd_330_, 1);
v___x_336_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_334_);
v___x_337_ = lean_uint64_of_nat(v_snd_335_);
v___x_338_ = lean_uint64_mix_hash(v___x_336_, v___x_337_);
v___x_339_ = lean_uint64_mix_hash(v___y_333_, v___x_338_);
v___x_340_ = 32ULL;
v___x_341_ = lean_uint64_shift_right(v___x_339_, v___x_340_);
v_fold_342_ = lean_uint64_xor(v___x_339_, v___x_341_);
v___x_343_ = 16ULL;
v___x_344_ = lean_uint64_shift_right(v_fold_342_, v___x_343_);
v___x_345_ = lean_uint64_xor(v_fold_342_, v___x_344_);
v___x_346_ = lean_uint64_to_usize(v___x_345_);
v___x_347_ = lean_usize_of_nat(v___x_331_);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_sub(v___x_347_, v___x_348_);
v___x_350_ = lean_usize_land(v___x_346_, v___x_349_);
v_bkt_351_ = lean_array_uget_borrowed(v_buckets_325_, v___x_350_);
v___x_352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_322_, v_bkt_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v_size_x27_354_; lean_object* v___x_355_; lean_object* v_buckets_x27_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v_size_x27_354_ = lean_nat_add(v_size_324_, v___x_353_);
lean_dec(v_size_324_);
lean_inc(v_bkt_351_);
v___x_355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_355_, 0, v_a_322_);
lean_ctor_set(v___x_355_, 1, v_b_323_);
lean_ctor_set(v___x_355_, 2, v_bkt_351_);
v_buckets_x27_356_ = lean_array_uset(v_buckets_325_, v___x_350_, v___x_355_);
v___x_357_ = lean_unsigned_to_nat(4u);
v___x_358_ = lean_nat_mul(v_size_x27_354_, v___x_357_);
v___x_359_ = lean_unsigned_to_nat(3u);
v___x_360_ = lean_nat_div(v___x_358_, v___x_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_array_get_size(v_buckets_x27_356_);
v___x_362_ = lean_nat_dec_le(v___x_360_, v___x_361_);
lean_dec(v___x_360_);
if (v___x_362_ == 0)
{
lean_object* v_val_363_; lean_object* v___x_365_; 
v_val_363_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_buckets_x27_356_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_val_363_);
lean_ctor_set(v___x_327_, 0, v_size_x27_354_);
v___x_365_ = v___x_327_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_size_x27_354_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_val_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
else
{
lean_object* v___x_368_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_buckets_x27_356_);
lean_ctor_set(v___x_327_, 0, v_size_x27_354_);
v___x_368_ = v___x_327_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_size_x27_354_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_buckets_x27_356_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v___x_370_; lean_object* v_buckets_x27_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
lean_inc(v_bkt_351_);
v___x_370_ = lean_box(0);
v_buckets_x27_371_ = lean_array_uset(v_buckets_325_, v___x_350_, v___x_370_);
v___x_372_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_322_, v_b_323_, v_bkt_351_);
v___x_373_ = lean_array_uset(v_buckets_x27_371_, v___x_350_, v___x_372_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_373_);
v___x_375_ = v___x_327_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_size_324_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object* v_specThm_382_, lean_object* v_info_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_396_; lean_object* v_proof_397_; lean_object* v_excessArgs_398_; lean_object* v_specBackwardRuleCache_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_key_404_; lean_object* v___x_405_; 
v___x_396_ = lean_st_ref_get(v_a_385_);
v_proof_397_ = lean_ctor_get(v_specThm_382_, 1);
v_excessArgs_398_ = lean_ctor_get(v_info_383_, 2);
v_specBackwardRuleCache_399_ = lean_ctor_get(v___x_396_, 0);
lean_inc_ref(v_specBackwardRuleCache_399_);
lean_dec(v___x_396_);
v___x_400_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key(v_proof_397_);
v___x_401_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(v_info_383_);
v___x_402_ = lean_array_get_size(v_excessArgs_398_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v_key_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_404_, 0, v___x_400_);
lean_ctor_set(v_key_404_, 1, v___x_403_);
v___x_405_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_399_, v_key_404_);
lean_dec_ref(v_specBackwardRuleCache_399_);
if (lean_obj_tag(v___x_405_) == 1)
{
lean_object* v___x_406_; 
lean_dec_ref_known(v_key_404_, 2);
lean_dec_ref(v_info_383_);
lean_dec_ref(v_specThm_382_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; lean_object* v___f_408_; uint8_t v___x_409_; lean_object* v___x_410_; 
lean_dec(v___x_405_);
v___x_407_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___closed__0));
v___f_408_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed), 15, 3);
lean_closure_set(v___f_408_, 0, v_specThm_382_);
lean_closure_set(v___f_408_, 1, v_info_383_);
lean_closure_set(v___f_408_, 2, v___x_407_);
v___x_409_ = 0;
v___x_410_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v___f_408_, v___x_409_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_446_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_446_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_446_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_446_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
if (lean_obj_tag(v_a_411_) == 0)
{
lean_object* v___x_415_; lean_object* v___x_417_; 
lean_dec_ref_known(v_key_404_, 2);
v___x_415_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
else
{
lean_object* v_val_419_; 
v_val_419_ = lean_ctor_get(v_a_411_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v_a_411_, 1);
if (lean_obj_tag(v_val_419_) == 1)
{
lean_object* v_val_420_; lean_object* v___x_421_; lean_object* v_specBackwardRuleCache_422_; lean_object* v_splitBackwardRuleCache_423_; lean_object* v_latticeBackwardRuleCache_424_; lean_object* v_invariants_425_; lean_object* v_vcs_426_; lean_object* v_simpState_427_; lean_object* v_fuel_428_; lean_object* v_inlineHandledInvariants_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_441_; 
v_val_420_ = lean_ctor_get(v_val_419_, 0);
v___x_421_ = lean_st_ref_take(v_a_385_);
v_specBackwardRuleCache_422_ = lean_ctor_get(v___x_421_, 0);
v_splitBackwardRuleCache_423_ = lean_ctor_get(v___x_421_, 1);
v_latticeBackwardRuleCache_424_ = lean_ctor_get(v___x_421_, 2);
v_invariants_425_ = lean_ctor_get(v___x_421_, 3);
v_vcs_426_ = lean_ctor_get(v___x_421_, 4);
v_simpState_427_ = lean_ctor_get(v___x_421_, 5);
v_fuel_428_ = lean_ctor_get(v___x_421_, 6);
v_inlineHandledInvariants_429_ = lean_ctor_get(v___x_421_, 7);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_441_ == 0)
{
v___x_431_ = v___x_421_;
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_inlineHandledInvariants_429_);
lean_inc(v_fuel_428_);
lean_inc(v_simpState_427_);
lean_inc(v_vcs_426_);
lean_inc(v_invariants_425_);
lean_inc(v_latticeBackwardRuleCache_424_);
lean_inc(v_splitBackwardRuleCache_423_);
lean_inc(v_specBackwardRuleCache_422_);
lean_dec(v___x_421_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
lean_inc(v_val_420_);
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_422_, v_key_404_, v_val_420_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_splitBackwardRuleCache_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_latticeBackwardRuleCache_424_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_invariants_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_vcs_426_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_simpState_427_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_fuel_428_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v_inlineHandledInvariants_429_);
v___x_435_ = v_reuseFailAlloc_440_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_st_ref_set(v_a_385_, v___x_435_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v_val_419_);
v___x_438_ = v___x_413_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_val_419_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_444_; 
lean_dec(v_val_419_);
lean_dec_ref_known(v_key_404_, 2);
v___x_442_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_442_);
v___x_444_ = v___x_413_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref_known(v_key_404_, 2);
v_a_447_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_410_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_410_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_455_, lean_object* v_info_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v_specThm_455_, v_info_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_470_, lean_object* v_m_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_471_, v_a_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_474_, lean_object* v_m_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_474_, v_m_475_, v_a_476_);
lean_dec_ref(v_a_476_);
lean_dec_ref(v_m_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_478_, lean_object* v_m_479_, lean_object* v_a_480_, lean_object* v_b_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_479_, v_a_480_, v_b_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_483_, lean_object* v_a_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_487_, lean_object* v_a_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_487_, v_a_488_, v_x_489_);
lean_dec(v_x_489_);
lean_dec_ref(v_a_488_);
return v_res_490_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_491_, lean_object* v_a_492_, lean_object* v_x_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_492_, v_x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_495_, lean_object* v_a_496_, lean_object* v_x_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_495_, v_a_496_, v_x_497_);
lean_dec(v_x_497_);
lean_dec_ref(v_a_496_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object* v_00_u03b2_500_, lean_object* v_data_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_data_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object* v_00_u03b2_503_, lean_object* v_a_504_, lean_object* v_b_505_, lean_object* v_x_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_504_, v_b_505_, v_x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_508_, lean_object* v_i_509_, lean_object* v_source_510_, lean_object* v_target_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v_i_509_, v_source_510_, v_target_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_x_514_, v_x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_523_, lean_object* v_info_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___y_532_; 
switch(lean_obj_tag(v_splitInfo_523_))
{
case 0:
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_532_ = v___x_576_;
goto v___jp_531_;
}
case 1:
{
lean_object* v___x_577_; 
v___x_577_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_532_ = v___x_577_;
goto v___jp_531_;
}
default: 
{
lean_object* v_matcherApp_578_; lean_object* v_matcherName_579_; 
v_matcherApp_578_ = lean_ctor_get(v_splitInfo_523_, 0);
v_matcherName_579_ = lean_ctor_get(v_matcherApp_578_, 1);
lean_inc(v_matcherName_579_);
v___y_532_ = v_matcherName_579_;
goto v___jp_531_;
}
}
v___jp_531_:
{
lean_object* v___x_533_; lean_object* v_excessArgs_534_; lean_object* v_splitBackwardRuleCache_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_key_539_; lean_object* v___x_540_; 
v___x_533_ = lean_st_ref_get(v_a_525_);
v_excessArgs_534_ = lean_ctor_get(v_info_524_, 2);
v_splitBackwardRuleCache_535_ = lean_ctor_get(v___x_533_, 1);
lean_inc_ref(v_splitBackwardRuleCache_535_);
lean_dec(v___x_533_);
v___x_536_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(v_info_524_);
v___x_537_ = lean_array_get_size(v_excessArgs_534_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v_key_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_539_, 0, v___y_532_);
lean_ctor_set(v_key_539_, 1, v___x_538_);
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_535_, v_key_539_);
lean_dec_ref(v_splitBackwardRuleCache_535_);
if (lean_obj_tag(v___x_540_) == 1)
{
lean_object* v_val_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref_known(v_key_539_, 2);
lean_dec_ref(v_info_524_);
lean_dec_ref(v_splitInfo_523_);
v_val_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_val_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_val_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v___x_549_; 
lean_dec(v___x_540_);
v___x_549_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(v_splitInfo_523_, v_info_524_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_575_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_575_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_575_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_575_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v_specBackwardRuleCache_555_; lean_object* v_splitBackwardRuleCache_556_; lean_object* v_latticeBackwardRuleCache_557_; lean_object* v_invariants_558_; lean_object* v_vcs_559_; lean_object* v_simpState_560_; lean_object* v_fuel_561_; lean_object* v_inlineHandledInvariants_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_574_; 
v___x_554_ = lean_st_ref_take(v_a_525_);
v_specBackwardRuleCache_555_ = lean_ctor_get(v___x_554_, 0);
v_splitBackwardRuleCache_556_ = lean_ctor_get(v___x_554_, 1);
v_latticeBackwardRuleCache_557_ = lean_ctor_get(v___x_554_, 2);
v_invariants_558_ = lean_ctor_get(v___x_554_, 3);
v_vcs_559_ = lean_ctor_get(v___x_554_, 4);
v_simpState_560_ = lean_ctor_get(v___x_554_, 5);
v_fuel_561_ = lean_ctor_get(v___x_554_, 6);
v_inlineHandledInvariants_562_ = lean_ctor_get(v___x_554_, 7);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_574_ == 0)
{
v___x_564_ = v___x_554_;
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_inlineHandledInvariants_562_);
lean_inc(v_fuel_561_);
lean_inc(v_simpState_560_);
lean_inc(v_vcs_559_);
lean_inc(v_invariants_558_);
lean_inc(v_latticeBackwardRuleCache_557_);
lean_inc(v_splitBackwardRuleCache_556_);
lean_inc(v_specBackwardRuleCache_555_);
lean_dec(v___x_554_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
lean_inc(v_a_550_);
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_556_, v_key_539_, v_a_550_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_specBackwardRuleCache_555_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_latticeBackwardRuleCache_557_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_invariants_558_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v_vcs_559_);
lean_ctor_set(v_reuseFailAlloc_573_, 5, v_simpState_560_);
lean_ctor_set(v_reuseFailAlloc_573_, 6, v_fuel_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 7, v_inlineHandledInvariants_562_);
v___x_568_ = v_reuseFailAlloc_573_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_st_ref_set(v_a_525_, v___x_568_);
if (v_isShared_553_ == 0)
{
v___x_571_ = v___x_552_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_550_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_539_, 2);
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object* v_splitInfo_580_, lean_object* v_info_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_580_, v_info_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(lean_object* v_splitInfo_589_, lean_object* v_info_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_589_, v_info_590_, v_a_592_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object* v_splitInfo_604_, lean_object* v_info_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_604_, v_info_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_618_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(lean_object* v_xs_619_, lean_object* v_ys_620_, lean_object* v_x_621_){
_start:
{
lean_object* v_zero_622_; uint8_t v_isZero_623_; 
v_zero_622_ = lean_unsigned_to_nat(0u);
v_isZero_623_ = lean_nat_dec_eq(v_x_621_, v_zero_622_);
if (v_isZero_623_ == 1)
{
lean_dec(v_x_621_);
return v_isZero_623_;
}
else
{
lean_object* v_one_624_; lean_object* v_n_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_one_624_ = lean_unsigned_to_nat(1u);
v_n_625_ = lean_nat_sub(v_x_621_, v_one_624_);
lean_dec(v_x_621_);
v___x_626_ = lean_array_fget_borrowed(v_xs_619_, v_n_625_);
v___x_627_ = lean_array_fget_borrowed(v_ys_620_, v_n_625_);
v___x_628_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_dec(v_n_625_);
return v___x_628_;
}
else
{
v_x_621_ = v_n_625_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_xs_630_, lean_object* v_ys_631_, lean_object* v_x_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_xs_630_, v_ys_631_, v_x_632_);
lean_dec_ref(v_ys_631_);
lean_dec_ref(v_xs_630_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(lean_object* v_a_635_, lean_object* v_x_636_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_box(0);
return v___x_637_;
}
else
{
lean_object* v_key_638_; lean_object* v_value_639_; lean_object* v_tail_640_; uint8_t v___y_642_; lean_object* v_fst_645_; lean_object* v_snd_646_; lean_object* v_fst_647_; lean_object* v_snd_648_; uint8_t v___x_649_; 
v_key_638_ = lean_ctor_get(v_x_636_, 0);
v_value_639_ = lean_ctor_get(v_x_636_, 1);
v_tail_640_ = lean_ctor_get(v_x_636_, 2);
v_fst_645_ = lean_ctor_get(v_key_638_, 0);
v_snd_646_ = lean_ctor_get(v_key_638_, 1);
v_fst_647_ = lean_ctor_get(v_a_635_, 0);
v_snd_648_ = lean_ctor_get(v_a_635_, 1);
v___x_649_ = lean_name_eq(v_fst_645_, v_fst_647_);
if (v___x_649_ == 0)
{
v___y_642_ = v___x_649_;
goto v___jp_641_;
}
else
{
lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_fst_650_ = lean_ctor_get(v_snd_646_, 0);
v_snd_651_ = lean_ctor_get(v_snd_646_, 1);
v_fst_652_ = lean_ctor_get(v_snd_648_, 0);
v_snd_653_ = lean_ctor_get(v_snd_648_, 1);
v___x_654_ = lean_array_get_size(v_fst_650_);
v___x_655_ = lean_array_get_size(v_fst_652_);
v___x_656_ = lean_nat_dec_eq(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
v_x_636_ = v_tail_640_;
goto _start;
}
else
{
uint8_t v___x_658_; 
v___x_658_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_fst_650_, v_fst_652_, v___x_654_);
if (v___x_658_ == 0)
{
v_x_636_ = v_tail_640_;
goto _start;
}
else
{
uint8_t v___x_660_; 
v___x_660_ = lean_nat_dec_eq(v_snd_651_, v_snd_653_);
v___y_642_ = v___x_660_;
goto v___jp_641_;
}
}
}
v___jp_641_:
{
if (v___y_642_ == 0)
{
v_x_636_ = v_tail_640_;
goto _start;
}
else
{
lean_object* v___x_644_; 
lean_inc(v_value_639_);
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v_value_639_);
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg___boxed(lean_object* v_a_661_, lean_object* v_x_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(v_a_661_, v_x_662_);
lean_dec(v_x_662_);
lean_dec_ref(v_a_661_);
return v_res_663_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(lean_object* v_as_664_, size_t v_i_665_, size_t v_stop_666_, uint64_t v_b_667_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = lean_usize_dec_eq(v_i_665_, v_stop_666_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; uint64_t v___x_670_; uint64_t v___x_671_; size_t v___x_672_; size_t v___x_673_; 
v___x_669_ = lean_array_uget_borrowed(v_as_664_, v_i_665_);
v___x_670_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v___x_669_);
v___x_671_ = lean_uint64_mix_hash(v_b_667_, v___x_670_);
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_add(v_i_665_, v___x_672_);
v_i_665_ = v___x_673_;
v_b_667_ = v___x_671_;
goto _start;
}
else
{
return v_b_667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3___boxed(lean_object* v_as_675_, lean_object* v_i_676_, lean_object* v_stop_677_, lean_object* v_b_678_){
_start:
{
size_t v_i_boxed_679_; size_t v_stop_boxed_680_; uint64_t v_b_boxed_681_; uint64_t v_res_682_; lean_object* v_r_683_; 
v_i_boxed_679_ = lean_unbox_usize(v_i_676_);
lean_dec(v_i_676_);
v_stop_boxed_680_ = lean_unbox_usize(v_stop_677_);
lean_dec(v_stop_677_);
v_b_boxed_681_ = lean_unbox_uint64(v_b_678_);
lean_dec_ref(v_b_678_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_as_675_, v_i_boxed_679_, v_stop_boxed_680_, v_b_boxed_681_);
lean_dec_ref(v_as_675_);
v_r_683_ = lean_box_uint64(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(lean_object* v_m_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_buckets_686_; lean_object* v_fst_687_; lean_object* v_snd_688_; lean_object* v___x_689_; lean_object* v___y_691_; uint64_t v___y_692_; uint64_t v___y_693_; uint64_t v___y_711_; 
v_buckets_686_ = lean_ctor_get(v_m_684_, 1);
v_fst_687_ = lean_ctor_get(v_a_685_, 0);
v_snd_688_ = lean_ctor_get(v_a_685_, 1);
v___x_689_ = lean_array_get_size(v_buckets_686_);
if (lean_obj_tag(v_fst_687_) == 0)
{
uint64_t v___x_725_; 
v___x_725_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_711_ = v___x_725_;
goto v___jp_710_;
}
else
{
uint64_t v_hash_726_; 
v_hash_726_ = lean_ctor_get_uint64(v_fst_687_, sizeof(void*)*2);
v___y_711_ = v_hash_726_;
goto v___jp_710_;
}
v___jp_690_:
{
uint64_t v___x_694_; uint64_t v___x_695_; uint64_t v___x_696_; uint64_t v___x_697_; uint64_t v___x_698_; uint64_t v_fold_699_; uint64_t v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; size_t v___x_703_; size_t v___x_704_; size_t v___x_705_; size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_694_ = lean_uint64_of_nat(v___y_691_);
v___x_695_ = lean_uint64_mix_hash(v___y_693_, v___x_694_);
v___x_696_ = lean_uint64_mix_hash(v___y_692_, v___x_695_);
v___x_697_ = 32ULL;
v___x_698_ = lean_uint64_shift_right(v___x_696_, v___x_697_);
v_fold_699_ = lean_uint64_xor(v___x_696_, v___x_698_);
v___x_700_ = 16ULL;
v___x_701_ = lean_uint64_shift_right(v_fold_699_, v___x_700_);
v___x_702_ = lean_uint64_xor(v_fold_699_, v___x_701_);
v___x_703_ = lean_uint64_to_usize(v___x_702_);
v___x_704_ = lean_usize_of_nat(v___x_689_);
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_sub(v___x_704_, v___x_705_);
v___x_707_ = lean_usize_land(v___x_703_, v___x_706_);
v___x_708_ = lean_array_uget_borrowed(v_buckets_686_, v___x_707_);
v___x_709_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(v_a_685_, v___x_708_);
return v___x_709_;
}
v___jp_710_:
{
lean_object* v_fst_712_; lean_object* v_snd_713_; uint64_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_fst_712_ = lean_ctor_get(v_snd_688_, 0);
v_snd_713_ = lean_ctor_get(v_snd_688_, 1);
v___x_714_ = 7ULL;
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_array_get_size(v_fst_712_);
v___x_717_ = lean_nat_dec_lt(v___x_715_, v___x_716_);
if (v___x_717_ == 0)
{
v___y_691_ = v_snd_713_;
v___y_692_ = v___y_711_;
v___y_693_ = v___x_714_;
goto v___jp_690_;
}
else
{
uint8_t v___x_718_; 
v___x_718_ = lean_nat_dec_le(v___x_716_, v___x_716_);
if (v___x_718_ == 0)
{
if (v___x_717_ == 0)
{
v___y_691_ = v_snd_713_;
v___y_692_ = v___y_711_;
v___y_693_ = v___x_714_;
goto v___jp_690_;
}
else
{
size_t v___x_719_; size_t v___x_720_; uint64_t v___x_721_; 
v___x_719_ = ((size_t)0ULL);
v___x_720_ = lean_usize_of_nat(v___x_716_);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_712_, v___x_719_, v___x_720_, v___x_714_);
v___y_691_ = v_snd_713_;
v___y_692_ = v___y_711_;
v___y_693_ = v___x_721_;
goto v___jp_690_;
}
}
else
{
size_t v___x_722_; size_t v___x_723_; uint64_t v___x_724_; 
v___x_722_ = ((size_t)0ULL);
v___x_723_ = lean_usize_of_nat(v___x_716_);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_712_, v___x_722_, v___x_723_, v___x_714_);
v___y_691_ = v_snd_713_;
v___y_692_ = v___y_711_;
v___y_693_ = v___x_724_;
goto v___jp_690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg___boxed(lean_object* v_m_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(v_m_727_, v_a_728_);
lean_dec_ref(v_a_728_);
lean_dec_ref(v_m_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg(size_t v_sz_730_, size_t v_i_731_, lean_object* v_bs_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = lean_usize_dec_lt(v_i_731_, v_sz_730_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_bs_732_);
return v___x_740_;
}
else
{
lean_object* v_v_741_; lean_object* v___x_742_; 
v_v_741_ = lean_array_uget_borrowed(v_bs_732_, v_i_731_);
lean_inc(v_v_741_);
v___x_742_ = l_Lean_Meta_Sym_inferType___redArg(v_v_741_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; lean_object* v_bs_x27_745_; size_t v___x_746_; size_t v___x_747_; lean_object* v___x_748_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v___x_744_ = lean_unsigned_to_nat(0u);
v_bs_x27_745_ = lean_array_uset(v_bs_732_, v_i_731_, v___x_744_);
v___x_746_ = ((size_t)1ULL);
v___x_747_ = lean_usize_add(v_i_731_, v___x_746_);
v___x_748_ = lean_array_uset(v_bs_x27_745_, v_i_731_, v_a_743_);
v_i_731_ = v___x_747_;
v_bs_732_ = v___x_748_;
goto _start;
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v_bs_732_);
v_a_750_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_742_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_742_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg___boxed(lean_object* v_sz_758_, lean_object* v_i_759_, lean_object* v_bs_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
size_t v_sz_boxed_767_; size_t v_i_boxed_768_; lean_object* v_res_769_; 
v_sz_boxed_767_ = lean_unbox_usize(v_sz_758_);
lean_dec(v_sz_758_);
v_i_boxed_768_ = lean_unbox_usize(v_i_759_);
lean_dec(v_i_759_);
v_res_769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg(v_sz_boxed_767_, v_i_boxed_768_, v_bs_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(size_t v_sz_770_, size_t v_i_771_, lean_object* v_bs_772_){
_start:
{
uint8_t v___x_773_; 
v___x_773_ = lean_usize_dec_lt(v_i_771_, v_sz_770_);
if (v___x_773_ == 0)
{
return v_bs_772_;
}
else
{
lean_object* v_v_774_; lean_object* v___x_775_; lean_object* v_bs_x27_776_; size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; 
v_v_774_ = lean_array_uget(v_bs_772_, v_i_771_);
v___x_775_ = lean_unsigned_to_nat(0u);
v_bs_x27_776_ = lean_array_uset(v_bs_772_, v_i_771_, v___x_775_);
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_add(v_i_771_, v___x_777_);
v___x_779_ = lean_array_uset(v_bs_x27_776_, v_i_771_, v_v_774_);
v_i_771_ = v___x_778_;
v_bs_772_ = v___x_779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___boxed(lean_object* v_sz_781_, lean_object* v_i_782_, lean_object* v_bs_783_){
_start:
{
size_t v_sz_boxed_784_; size_t v_i_boxed_785_; lean_object* v_res_786_; 
v_sz_boxed_784_ = lean_unbox_usize(v_sz_781_);
lean_dec(v_sz_781_);
v_i_boxed_785_ = lean_unbox_usize(v_i_782_);
lean_dec(v_i_782_);
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(v_sz_boxed_784_, v_i_boxed_785_, v_bs_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9___redArg(lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
if (lean_obj_tag(v_x_788_) == 0)
{
return v_x_787_;
}
else
{
lean_object* v_key_789_; lean_object* v_value_790_; lean_object* v_tail_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_839_; 
v_key_789_ = lean_ctor_get(v_x_788_, 0);
v_value_790_ = lean_ctor_get(v_x_788_, 1);
v_tail_791_ = lean_ctor_get(v_x_788_, 2);
v_isSharedCheck_839_ = !lean_is_exclusive(v_x_788_);
if (v_isSharedCheck_839_ == 0)
{
v___x_793_ = v_x_788_;
v_isShared_794_ = v_isSharedCheck_839_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_tail_791_);
lean_inc(v_value_790_);
lean_inc(v_key_789_);
lean_dec(v_x_788_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_839_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_fst_795_; lean_object* v_snd_796_; lean_object* v___x_797_; lean_object* v___y_799_; uint64_t v___y_800_; uint64_t v___y_801_; uint64_t v___y_823_; 
v_fst_795_ = lean_ctor_get(v_key_789_, 0);
v_snd_796_ = lean_ctor_get(v_key_789_, 1);
v___x_797_ = lean_array_get_size(v_x_787_);
if (lean_obj_tag(v_fst_795_) == 0)
{
uint64_t v___x_837_; 
v___x_837_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_823_ = v___x_837_;
goto v___jp_822_;
}
else
{
uint64_t v_hash_838_; 
v_hash_838_ = lean_ctor_get_uint64(v_fst_795_, sizeof(void*)*2);
v___y_823_ = v_hash_838_;
goto v___jp_822_;
}
v___jp_798_:
{
uint64_t v___x_802_; uint64_t v___x_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v_fold_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v___x_810_; size_t v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_802_ = lean_uint64_of_nat(v___y_799_);
lean_dec(v___y_799_);
v___x_803_ = lean_uint64_mix_hash(v___y_801_, v___x_802_);
v___x_804_ = lean_uint64_mix_hash(v___y_800_, v___x_803_);
v___x_805_ = 32ULL;
v___x_806_ = lean_uint64_shift_right(v___x_804_, v___x_805_);
v_fold_807_ = lean_uint64_xor(v___x_804_, v___x_806_);
v___x_808_ = 16ULL;
v___x_809_ = lean_uint64_shift_right(v_fold_807_, v___x_808_);
v___x_810_ = lean_uint64_xor(v_fold_807_, v___x_809_);
v___x_811_ = lean_uint64_to_usize(v___x_810_);
v___x_812_ = lean_usize_of_nat(v___x_797_);
v___x_813_ = ((size_t)1ULL);
v___x_814_ = lean_usize_sub(v___x_812_, v___x_813_);
v___x_815_ = lean_usize_land(v___x_811_, v___x_814_);
v___x_816_ = lean_array_uget_borrowed(v_x_787_, v___x_815_);
lean_inc(v___x_816_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 2, v___x_816_);
v___x_818_ = v___x_793_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_key_789_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_value_790_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v___x_816_);
v___x_818_ = v_reuseFailAlloc_821_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; 
v___x_819_ = lean_array_uset(v_x_787_, v___x_815_, v___x_818_);
v_x_787_ = v___x_819_;
v_x_788_ = v_tail_791_;
goto _start;
}
}
v___jp_822_:
{
lean_object* v_fst_824_; lean_object* v_snd_825_; uint64_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v_fst_824_ = lean_ctor_get(v_snd_796_, 0);
v_snd_825_ = lean_ctor_get(v_snd_796_, 1);
v___x_826_ = 7ULL;
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_array_get_size(v_fst_824_);
v___x_829_ = lean_nat_dec_lt(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_inc(v_snd_825_);
v___y_799_ = v_snd_825_;
v___y_800_ = v___y_823_;
v___y_801_ = v___x_826_;
goto v___jp_798_;
}
else
{
uint8_t v___x_830_; 
v___x_830_ = lean_nat_dec_le(v___x_828_, v___x_828_);
if (v___x_830_ == 0)
{
if (v___x_829_ == 0)
{
lean_inc(v_snd_825_);
v___y_799_ = v_snd_825_;
v___y_800_ = v___y_823_;
v___y_801_ = v___x_826_;
goto v___jp_798_;
}
else
{
size_t v___x_831_; size_t v___x_832_; uint64_t v___x_833_; 
v___x_831_ = ((size_t)0ULL);
v___x_832_ = lean_usize_of_nat(v___x_828_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_824_, v___x_831_, v___x_832_, v___x_826_);
lean_inc(v_snd_825_);
v___y_799_ = v_snd_825_;
v___y_800_ = v___y_823_;
v___y_801_ = v___x_833_;
goto v___jp_798_;
}
}
else
{
size_t v___x_834_; size_t v___x_835_; uint64_t v___x_836_; 
v___x_834_ = ((size_t)0ULL);
v___x_835_ = lean_usize_of_nat(v___x_828_);
v___x_836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_824_, v___x_834_, v___x_835_, v___x_826_);
lean_inc(v_snd_825_);
v___y_799_ = v_snd_825_;
v___y_800_ = v___y_823_;
v___y_801_ = v___x_836_;
goto v___jp_798_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8___redArg(lean_object* v_i_840_, lean_object* v_source_841_, lean_object* v_target_842_){
_start:
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = lean_array_get_size(v_source_841_);
v___x_844_ = lean_nat_dec_lt(v_i_840_, v___x_843_);
if (v___x_844_ == 0)
{
lean_dec_ref(v_source_841_);
lean_dec(v_i_840_);
return v_target_842_;
}
else
{
lean_object* v_es_845_; lean_object* v___x_846_; lean_object* v_source_847_; lean_object* v_target_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_es_845_ = lean_array_fget(v_source_841_, v_i_840_);
v___x_846_ = lean_box(0);
v_source_847_ = lean_array_fset(v_source_841_, v_i_840_, v___x_846_);
v_target_848_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9___redArg(v_target_842_, v_es_845_);
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_add(v_i_840_, v___x_849_);
lean_dec(v_i_840_);
v_i_840_ = v___x_850_;
v_source_841_ = v_source_847_;
v_target_842_ = v_target_848_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6___redArg(lean_object* v_data_852_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v_nbuckets_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_853_ = lean_array_get_size(v_data_852_);
v___x_854_ = lean_unsigned_to_nat(2u);
v_nbuckets_855_ = lean_nat_mul(v___x_853_, v___x_854_);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_box(0);
v___x_858_ = lean_mk_array(v_nbuckets_855_, v___x_857_);
v___x_859_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8___redArg(v___x_856_, v_data_852_, v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(lean_object* v_a_860_, lean_object* v_b_861_, lean_object* v_x_862_){
_start:
{
if (lean_obj_tag(v_x_862_) == 0)
{
lean_dec(v_b_861_);
lean_dec_ref(v_a_860_);
return v_x_862_;
}
else
{
lean_object* v_key_863_; lean_object* v_value_864_; lean_object* v_tail_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_891_; 
v_key_863_ = lean_ctor_get(v_x_862_, 0);
v_value_864_ = lean_ctor_get(v_x_862_, 1);
v_tail_865_ = lean_ctor_get(v_x_862_, 2);
v_isSharedCheck_891_ = !lean_is_exclusive(v_x_862_);
if (v_isSharedCheck_891_ == 0)
{
v___x_867_ = v_x_862_;
v_isShared_868_ = v_isSharedCheck_891_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_tail_865_);
lean_inc(v_value_864_);
lean_inc(v_key_863_);
lean_dec(v_x_862_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_891_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint8_t v___y_875_; lean_object* v_fst_877_; lean_object* v_snd_878_; lean_object* v_fst_879_; lean_object* v_snd_880_; uint8_t v___x_881_; 
v_fst_877_ = lean_ctor_get(v_key_863_, 0);
v_snd_878_ = lean_ctor_get(v_key_863_, 1);
v_fst_879_ = lean_ctor_get(v_a_860_, 0);
v_snd_880_ = lean_ctor_get(v_a_860_, 1);
v___x_881_ = lean_name_eq(v_fst_877_, v_fst_879_);
if (v___x_881_ == 0)
{
v___y_875_ = v___x_881_;
goto v___jp_874_;
}
else
{
lean_object* v_fst_882_; lean_object* v_snd_883_; lean_object* v_fst_884_; lean_object* v_snd_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_fst_882_ = lean_ctor_get(v_snd_878_, 0);
v_snd_883_ = lean_ctor_get(v_snd_878_, 1);
v_fst_884_ = lean_ctor_get(v_snd_880_, 0);
v_snd_885_ = lean_ctor_get(v_snd_880_, 1);
v___x_886_ = lean_array_get_size(v_fst_882_);
v___x_887_ = lean_array_get_size(v_fst_884_);
v___x_888_ = lean_nat_dec_eq(v___x_886_, v___x_887_);
if (v___x_888_ == 0)
{
goto v___jp_869_;
}
else
{
uint8_t v___x_889_; 
v___x_889_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_fst_882_, v_fst_884_, v___x_886_);
if (v___x_889_ == 0)
{
goto v___jp_869_;
}
else
{
uint8_t v___x_890_; 
v___x_890_ = lean_nat_dec_eq(v_snd_883_, v_snd_885_);
v___y_875_ = v___x_890_;
goto v___jp_874_;
}
}
}
v___jp_869_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(v_a_860_, v_b_861_, v_tail_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 2, v___x_870_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_key_863_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_value_864_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
v___jp_874_:
{
if (v___y_875_ == 0)
{
goto v___jp_869_;
}
else
{
lean_object* v___x_876_; 
lean_del_object(v___x_867_);
lean_dec(v_value_864_);
lean_dec(v_key_863_);
v___x_876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_876_, 0, v_a_860_);
lean_ctor_set(v___x_876_, 1, v_b_861_);
lean_ctor_set(v___x_876_, 2, v_tail_865_);
return v___x_876_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(lean_object* v_a_892_, lean_object* v_x_893_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
uint8_t v___x_894_; 
v___x_894_ = 0;
return v___x_894_;
}
else
{
lean_object* v_key_895_; lean_object* v_tail_896_; uint8_t v___y_898_; lean_object* v_fst_900_; lean_object* v_snd_901_; lean_object* v_fst_902_; lean_object* v_snd_903_; uint8_t v___x_904_; 
v_key_895_ = lean_ctor_get(v_x_893_, 0);
v_tail_896_ = lean_ctor_get(v_x_893_, 2);
v_fst_900_ = lean_ctor_get(v_key_895_, 0);
v_snd_901_ = lean_ctor_get(v_key_895_, 1);
v_fst_902_ = lean_ctor_get(v_a_892_, 0);
v_snd_903_ = lean_ctor_get(v_a_892_, 1);
v___x_904_ = lean_name_eq(v_fst_900_, v_fst_902_);
if (v___x_904_ == 0)
{
v___y_898_ = v___x_904_;
goto v___jp_897_;
}
else
{
lean_object* v_fst_905_; lean_object* v_snd_906_; lean_object* v_fst_907_; lean_object* v_snd_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_fst_905_ = lean_ctor_get(v_snd_901_, 0);
v_snd_906_ = lean_ctor_get(v_snd_901_, 1);
v_fst_907_ = lean_ctor_get(v_snd_903_, 0);
v_snd_908_ = lean_ctor_get(v_snd_903_, 1);
v___x_909_ = lean_array_get_size(v_fst_905_);
v___x_910_ = lean_array_get_size(v_fst_907_);
v___x_911_ = lean_nat_dec_eq(v___x_909_, v___x_910_);
if (v___x_911_ == 0)
{
v_x_893_ = v_tail_896_;
goto _start;
}
else
{
uint8_t v___x_913_; 
v___x_913_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_fst_905_, v_fst_907_, v___x_909_);
if (v___x_913_ == 0)
{
v_x_893_ = v_tail_896_;
goto _start;
}
else
{
uint8_t v___x_915_; 
v___x_915_ = lean_nat_dec_eq(v_snd_906_, v_snd_908_);
v___y_898_ = v___x_915_;
goto v___jp_897_;
}
}
}
v___jp_897_:
{
if (v___y_898_ == 0)
{
v_x_893_ = v_tail_896_;
goto _start;
}
else
{
return v___y_898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg___boxed(lean_object* v_a_916_, lean_object* v_x_917_){
_start:
{
uint8_t v_res_918_; lean_object* v_r_919_; 
v_res_918_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(v_a_916_, v_x_917_);
lean_dec(v_x_917_);
lean_dec_ref(v_a_916_);
v_r_919_ = lean_box(v_res_918_);
return v_r_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3___redArg(lean_object* v_m_920_, lean_object* v_a_921_, lean_object* v_b_922_){
_start:
{
lean_object* v_size_923_; lean_object* v_buckets_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_992_; 
v_size_923_ = lean_ctor_get(v_m_920_, 0);
v_buckets_924_ = lean_ctor_get(v_m_920_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_m_920_);
if (v_isSharedCheck_992_ == 0)
{
v___x_926_ = v_m_920_;
v_isShared_927_ = v_isSharedCheck_992_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_buckets_924_);
lean_inc(v_size_923_);
lean_dec(v_m_920_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_992_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_fst_928_; lean_object* v_snd_929_; lean_object* v___x_930_; lean_object* v___y_932_; uint64_t v___y_933_; uint64_t v___y_934_; uint64_t v___y_976_; 
v_fst_928_ = lean_ctor_get(v_a_921_, 0);
v_snd_929_ = lean_ctor_get(v_a_921_, 1);
v___x_930_ = lean_array_get_size(v_buckets_924_);
if (lean_obj_tag(v_fst_928_) == 0)
{
uint64_t v___x_990_; 
v___x_990_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_976_ = v___x_990_;
goto v___jp_975_;
}
else
{
uint64_t v_hash_991_; 
v_hash_991_ = lean_ctor_get_uint64(v_fst_928_, sizeof(void*)*2);
v___y_976_ = v_hash_991_;
goto v___jp_975_;
}
v___jp_931_:
{
uint64_t v___x_935_; uint64_t v___x_936_; uint64_t v___x_937_; uint64_t v___x_938_; uint64_t v___x_939_; uint64_t v_fold_940_; uint64_t v___x_941_; uint64_t v___x_942_; uint64_t v___x_943_; size_t v___x_944_; size_t v___x_945_; size_t v___x_946_; size_t v___x_947_; size_t v___x_948_; lean_object* v_bkt_949_; uint8_t v___x_950_; 
v___x_935_ = lean_uint64_of_nat(v___y_932_);
lean_dec(v___y_932_);
v___x_936_ = lean_uint64_mix_hash(v___y_934_, v___x_935_);
v___x_937_ = lean_uint64_mix_hash(v___y_933_, v___x_936_);
v___x_938_ = 32ULL;
v___x_939_ = lean_uint64_shift_right(v___x_937_, v___x_938_);
v_fold_940_ = lean_uint64_xor(v___x_937_, v___x_939_);
v___x_941_ = 16ULL;
v___x_942_ = lean_uint64_shift_right(v_fold_940_, v___x_941_);
v___x_943_ = lean_uint64_xor(v_fold_940_, v___x_942_);
v___x_944_ = lean_uint64_to_usize(v___x_943_);
v___x_945_ = lean_usize_of_nat(v___x_930_);
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_sub(v___x_945_, v___x_946_);
v___x_948_ = lean_usize_land(v___x_944_, v___x_947_);
v_bkt_949_ = lean_array_uget_borrowed(v_buckets_924_, v___x_948_);
v___x_950_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(v_a_921_, v_bkt_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v_size_x27_952_; lean_object* v___x_953_; lean_object* v_buckets_x27_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_951_ = lean_unsigned_to_nat(1u);
v_size_x27_952_ = lean_nat_add(v_size_923_, v___x_951_);
lean_dec(v_size_923_);
lean_inc(v_bkt_949_);
v___x_953_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_953_, 0, v_a_921_);
lean_ctor_set(v___x_953_, 1, v_b_922_);
lean_ctor_set(v___x_953_, 2, v_bkt_949_);
v_buckets_x27_954_ = lean_array_uset(v_buckets_924_, v___x_948_, v___x_953_);
v___x_955_ = lean_unsigned_to_nat(4u);
v___x_956_ = lean_nat_mul(v_size_x27_952_, v___x_955_);
v___x_957_ = lean_unsigned_to_nat(3u);
v___x_958_ = lean_nat_div(v___x_956_, v___x_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_array_get_size(v_buckets_x27_954_);
v___x_960_ = lean_nat_dec_le(v___x_958_, v___x_959_);
lean_dec(v___x_958_);
if (v___x_960_ == 0)
{
lean_object* v_val_961_; lean_object* v___x_963_; 
v_val_961_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6___redArg(v_buckets_x27_954_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v_val_961_);
lean_ctor_set(v___x_926_, 0, v_size_x27_952_);
v___x_963_ = v___x_926_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_size_x27_952_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_val_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
else
{
lean_object* v___x_966_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v_buckets_x27_954_);
lean_ctor_set(v___x_926_, 0, v_size_x27_952_);
v___x_966_ = v___x_926_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_size_x27_952_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_buckets_x27_954_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
else
{
lean_object* v___x_968_; lean_object* v_buckets_x27_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
lean_inc(v_bkt_949_);
v___x_968_ = lean_box(0);
v_buckets_x27_969_ = lean_array_uset(v_buckets_924_, v___x_948_, v___x_968_);
v___x_970_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(v_a_921_, v_b_922_, v_bkt_949_);
v___x_971_ = lean_array_uset(v_buckets_x27_969_, v___x_948_, v___x_970_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_971_);
v___x_973_ = v___x_926_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_size_923_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
v___jp_975_:
{
lean_object* v_fst_977_; lean_object* v_snd_978_; uint64_t v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v_fst_977_ = lean_ctor_get(v_snd_929_, 0);
v_snd_978_ = lean_ctor_get(v_snd_929_, 1);
v___x_979_ = 7ULL;
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_array_get_size(v_fst_977_);
v___x_982_ = lean_nat_dec_lt(v___x_980_, v___x_981_);
if (v___x_982_ == 0)
{
lean_inc(v_snd_978_);
v___y_932_ = v_snd_978_;
v___y_933_ = v___y_976_;
v___y_934_ = v___x_979_;
goto v___jp_931_;
}
else
{
uint8_t v___x_983_; 
v___x_983_ = lean_nat_dec_le(v___x_981_, v___x_981_);
if (v___x_983_ == 0)
{
if (v___x_982_ == 0)
{
lean_inc(v_snd_978_);
v___y_932_ = v_snd_978_;
v___y_933_ = v___y_976_;
v___y_934_ = v___x_979_;
goto v___jp_931_;
}
else
{
size_t v___x_984_; size_t v___x_985_; uint64_t v___x_986_; 
v___x_984_ = ((size_t)0ULL);
v___x_985_ = lean_usize_of_nat(v___x_981_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_977_, v___x_984_, v___x_985_, v___x_979_);
lean_inc(v_snd_978_);
v___y_932_ = v_snd_978_;
v___y_933_ = v___y_976_;
v___y_934_ = v___x_986_;
goto v___jp_931_;
}
}
else
{
size_t v___x_987_; size_t v___x_988_; uint64_t v___x_989_; 
v___x_987_ = ((size_t)0ULL);
v___x_988_ = lean_usize_of_nat(v___x_981_);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_977_, v___x_987_, v___x_988_, v___x_979_);
lean_inc(v_snd_978_);
v___y_932_ = v_snd_978_;
v___y_933_ = v___y_976_;
v___y_934_ = v___x_989_;
goto v___jp_931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(lean_object* v_c_993_, lean_object* v_as_994_, lean_object* v_excessArgs_995_, lean_object* v_resultType_x3f_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1005_; size_t v_sz_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
v___x_1005_ = lean_st_ref_get(v_a_997_);
v_sz_1006_ = lean_array_size(v_as_994_);
v___x_1007_ = ((size_t)0ULL);
lean_inc_ref(v_as_994_);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg(v_sz_1006_, v___x_1007_, v_as_994_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1052_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1052_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1052_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v_latticeBackwardRuleCache_1013_; lean_object* v_applyLemma_1014_; size_t v_sz_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_latticeBackwardRuleCache_1013_ = lean_ctor_get(v___x_1005_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_1013_);
lean_dec(v___x_1005_);
v_applyLemma_1014_ = lean_ctor_get(v_c_993_, 1);
v_sz_1015_ = lean_array_size(v_a_1009_);
v___x_1016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(v_sz_1015_, v___x_1007_, v_a_1009_);
v___x_1017_ = lean_array_get_size(v_excessArgs_995_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
lean_inc(v_applyLemma_1014_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_applyLemma_1014_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(v_latticeBackwardRuleCache_1013_, v___x_1019_);
lean_dec_ref(v_latticeBackwardRuleCache_1013_);
if (lean_obj_tag(v___x_1020_) == 1)
{
lean_object* v_val_1021_; lean_object* v___x_1023_; 
lean_dec_ref_known(v___x_1019_, 2);
lean_dec(v_resultType_x3f_996_);
lean_dec_ref(v_excessArgs_995_);
lean_dec_ref(v_as_994_);
lean_dec_ref(v_c_993_);
v_val_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_val_1021_);
lean_dec_ref_known(v___x_1020_, 1);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_val_1021_);
v___x_1023_ = v___x_1011_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_val_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
else
{
lean_object* v___x_1025_; 
lean_dec(v___x_1020_);
lean_del_object(v___x_1011_);
v___x_1025_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeSplit_mkBackwardRuleForLattice(v_c_993_, v_as_994_, v_excessArgs_995_, v_resultType_x3f_996_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1051_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1051_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1051_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v_specBackwardRuleCache_1031_; lean_object* v_splitBackwardRuleCache_1032_; lean_object* v_latticeBackwardRuleCache_1033_; lean_object* v_invariants_1034_; lean_object* v_vcs_1035_; lean_object* v_simpState_1036_; lean_object* v_fuel_1037_; lean_object* v_inlineHandledInvariants_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1050_; 
v___x_1030_ = lean_st_ref_take(v_a_997_);
v_specBackwardRuleCache_1031_ = lean_ctor_get(v___x_1030_, 0);
v_splitBackwardRuleCache_1032_ = lean_ctor_get(v___x_1030_, 1);
v_latticeBackwardRuleCache_1033_ = lean_ctor_get(v___x_1030_, 2);
v_invariants_1034_ = lean_ctor_get(v___x_1030_, 3);
v_vcs_1035_ = lean_ctor_get(v___x_1030_, 4);
v_simpState_1036_ = lean_ctor_get(v___x_1030_, 5);
v_fuel_1037_ = lean_ctor_get(v___x_1030_, 6);
v_inlineHandledInvariants_1038_ = lean_ctor_get(v___x_1030_, 7);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1040_ = v___x_1030_;
v_isShared_1041_ = v_isSharedCheck_1050_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_inlineHandledInvariants_1038_);
lean_inc(v_fuel_1037_);
lean_inc(v_simpState_1036_);
lean_inc(v_vcs_1035_);
lean_inc(v_invariants_1034_);
lean_inc(v_latticeBackwardRuleCache_1033_);
lean_inc(v_splitBackwardRuleCache_1032_);
lean_inc(v_specBackwardRuleCache_1031_);
lean_dec(v___x_1030_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1050_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_inc(v_a_1026_);
v___x_1042_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3___redArg(v_latticeBackwardRuleCache_1033_, v___x_1019_, v_a_1026_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 2, v___x_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_specBackwardRuleCache_1031_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_splitBackwardRuleCache_1032_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_invariants_1034_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_vcs_1035_);
lean_ctor_set(v_reuseFailAlloc_1049_, 5, v_simpState_1036_);
lean_ctor_set(v_reuseFailAlloc_1049_, 6, v_fuel_1037_);
lean_ctor_set(v_reuseFailAlloc_1049_, 7, v_inlineHandledInvariants_1038_);
v___x_1044_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_st_ref_set(v_a_997_, v___x_1044_);
if (v_isShared_1029_ == 0)
{
v___x_1047_ = v___x_1028_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1026_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_1019_, 2);
return v___x_1025_;
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v___x_1005_);
lean_dec(v_resultType_x3f_996_);
lean_dec_ref(v_excessArgs_995_);
lean_dec_ref(v_as_994_);
lean_dec_ref(v_c_993_);
v_a_1053_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1008_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1008_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg___boxed(lean_object* v_c_1061_, lean_object* v_as_1062_, lean_object* v_excessArgs_1063_, lean_object* v_resultType_x3f_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(v_c_1061_, v_as_1062_, v_excessArgs_1063_, v_resultType_x3f_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached(lean_object* v_c_1074_, lean_object* v_as_1075_, lean_object* v_excessArgs_1076_, lean_object* v_resultType_x3f_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(v_c_1074_, v_as_1075_, v_excessArgs_1076_, v_resultType_x3f_1077_, v_a_1079_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___boxed(lean_object* v_c_1091_, lean_object* v_as_1092_, lean_object* v_excessArgs_1093_, lean_object* v_resultType_x3f_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached(v_c_1091_, v_as_1092_, v_excessArgs_1093_, v_resultType_x3f_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(size_t v_sz_1108_, size_t v_i_1109_, lean_object* v_bs_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg(v_sz_1108_, v_i_1109_, v_bs_1110_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___boxed(lean_object* v_sz_1119_, lean_object* v_i_1120_, lean_object* v_bs_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
size_t v_sz_boxed_1129_; size_t v_i_boxed_1130_; lean_object* v_res_1131_; 
v_sz_boxed_1129_ = lean_unbox_usize(v_sz_1119_);
lean_dec(v_sz_1119_);
v_i_boxed_1130_ = lean_unbox_usize(v_i_1120_);
lean_dec(v_i_1120_);
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(v_sz_boxed_1129_, v_i_boxed_1130_, v_bs_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2(lean_object* v_00_u03b2_1132_, lean_object* v_m_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(v_m_1133_, v_a_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___boxed(lean_object* v_00_u03b2_1136_, lean_object* v_m_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2(v_00_u03b2_1136_, v_m_1137_, v_a_1138_);
lean_dec_ref(v_a_1138_);
lean_dec_ref(v_m_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3(lean_object* v_00_u03b2_1140_, lean_object* v_m_1141_, lean_object* v_a_1142_, lean_object* v_b_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3___redArg(v_m_1141_, v_a_1142_, v_b_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2(lean_object* v_00_u03b2_1145_, lean_object* v_a_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(v_a_1146_, v_x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1149_, lean_object* v_a_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2(v_00_u03b2_1149_, v_a_1150_, v_x_1151_);
lean_dec(v_x_1151_);
lean_dec_ref(v_a_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5(lean_object* v_00_u03b2_1153_, lean_object* v_a_1154_, lean_object* v_x_1155_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(v_a_1154_, v_x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1157_, lean_object* v_a_1158_, lean_object* v_x_1159_){
_start:
{
uint8_t v_res_1160_; lean_object* v_r_1161_; 
v_res_1160_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5(v_00_u03b2_1157_, v_a_1158_, v_x_1159_);
lean_dec(v_x_1159_);
lean_dec_ref(v_a_1158_);
v_r_1161_ = lean_box(v_res_1160_);
return v_r_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6(lean_object* v_00_u03b2_1162_, lean_object* v_data_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6___redArg(v_data_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7(lean_object* v_00_u03b2_1165_, lean_object* v_a_1166_, lean_object* v_b_1167_, lean_object* v_x_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(v_a_1166_, v_b_1167_, v_x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3(lean_object* v_xs_1170_, lean_object* v_ys_1171_, lean_object* v_hsz_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
uint8_t v___x_1175_; 
v___x_1175_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_xs_1170_, v_ys_1171_, v_x_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___boxed(lean_object* v_xs_1176_, lean_object* v_ys_1177_, lean_object* v_hsz_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
uint8_t v_res_1181_; lean_object* v_r_1182_; 
v_res_1181_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3(v_xs_1176_, v_ys_1177_, v_hsz_1178_, v_x_1179_, v_x_1180_);
lean_dec_ref(v_ys_1177_);
lean_dec_ref(v_xs_1176_);
v_r_1182_ = lean_box(v_res_1181_);
return v_r_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1183_, lean_object* v_i_1184_, lean_object* v_source_1185_, lean_object* v_target_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8___redArg(v_i_1184_, v_source_1185_, v_target_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9___redArg(v_x_1189_, v_x_1190_);
return v___x_1191_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
}
#ifdef __cplusplus
}
#endif
