// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Attr
// Imports: public import Lean.Meta.Tactic.Grind.Injective public import Lean.Meta.Tactic.Grind.Cases public import Lean.Meta.Tactic.Grind.ExtAttr public import Lean.Meta.Tactic.Simp.Attr public import Lean.Meta.Tactic.Grind.Homo import Lean.Meta.Sym.Simp.Attr import Lean.ExtraModUses
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkExtension(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Meta_addDeclToUnfold(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_homoExt;
lean_object* l_Lean_Meta_Grind_validateHomoTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateExtAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSymbolPriorityAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "normExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 117, 24, 11, 244, 218, 170, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "unexpected `grind` theorem kind: `"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__5;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__7;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindEq"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(179, 34, 219, 24, 240, 38, 65, 204)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindDef"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(66, 218, 12, 28, 39, 29, 4, 77)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindFwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value),LEAN_SCALAR_PTR_LITERAL(121, 161, 177, 116, 112, 162, 92, 47)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value),LEAN_SCALAR_PTR_LITERAL(114, 163, 57, 243, 160, 41, 114, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqRhs"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value),LEAN_SCALAR_PTR_LITERAL(222, 187, 148, 221, 105, 213, 199, 68)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindEqBoth"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value),LEAN_SCALAR_PTR_LITERAL(79, 230, 133, 190, 186, 228, 109, 128)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value),LEAN_SCALAR_PTR_LITERAL(250, 57, 23, 180, 238, 116, 90, 53)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindLR"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value),LEAN_SCALAR_PTR_LITERAL(152, 111, 188, 78, 132, 212, 97, 164)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindRL"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value),LEAN_SCALAR_PTR_LITERAL(84, 112, 237, 169, 105, 148, 42, 205)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindUsr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value),LEAN_SCALAR_PTR_LITERAL(204, 58, 160, 148, 192, 167, 114, 18)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindGen"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value),LEAN_SCALAR_PTR_LITERAL(186, 203, 120, 147, 97, 215, 208, 134)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindCases"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value),LEAN_SCALAR_PTR_LITERAL(85, 142, 28, 230, 49, 50, 229, 162)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grindCasesEager"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value),LEAN_SCALAR_PTR_LITERAL(75, 210, 92, 40, 190, 183, 142, 70)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindIntro"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value),LEAN_SCALAR_PTR_LITERAL(142, 126, 114, 89, 237, 253, 56, 138)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindExt"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(147, 193, 153, 166, 243, 149, 163, 253)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindInj"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 41, 9, 21, 5, 145, 193)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindFunCC"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value),LEAN_SCALAR_PTR_LITERAL(217, 20, 186, 134, 249, 79, 78, 43)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindNorm"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value),LEAN_SCALAR_PTR_LITERAL(166, 126, 146, 239, 104, 253, 29, 148)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindUnfold"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value),LEAN_SCALAR_PTR_LITERAL(214, 181, 37, 92, 122, 232, 164, 219)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindHomo"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value),LEAN_SCALAR_PTR_LITERAL(88, 142, 231, 82, 214, 226, 8, 218)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindHomoPred"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value),LEAN_SCALAR_PTR_LITERAL(205, 178, 67, 251, 213, 77, 25, 210)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__51 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "priority expected"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__54 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__55 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__58 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__59 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__60 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__61 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__62 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__63 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__63_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__64 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__65 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__65_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "the modifier `usr` is only relevant in parameters for `grind only`"};
static const lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "\?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "]` instead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "cannot mark declaration to be unfolded by `grind`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind homo"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_validateHomoTheorem___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "invalid `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " intro]`, `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "symbol priorities must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "normalizer must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "declaration to unfold must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "homomorphism rules must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "homomorphism predicates must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "When applied to an equational theorem, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " =]`, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " =_]`, or `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = " _=_]`will mark the theorem for use in heuristic instantiations by the `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 135, .m_data = "` tactic,\n      using respectively the left-hand side, the right-hand side, or both sides of the theorem.When applied to a function, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 112, .m_capacity = 112, .m_length = 111, .m_data = " =]` automatically annotates the equational theorems associated with that function.When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 183, .m_capacity = 183, .m_length = 180, .m_data = " ←]` will instantiate the theorem whenever it encounters the conclusion of the theorem\n      (that is, it will use the theorem for backwards reasoning).When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 190, .m_capacity = 190, .m_length = 187, .m_data = " →]` will instantiate the theorem whenever it encounters sufficiently many of the propositional hypotheses\n      (that is, it will use the theorem for forwards reasoning).The attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "]` by itself will effectively try `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 68, .m_data = " ←]` (if the conclusion is sufficient for instantiation) and then `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 162, .m_data = " →]`.The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.For example, if a theorem `@["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 179, .m_capacity = 179, .m_length = 178, .m_data = " =] theorem foo_idempotent : foo (foo x) = foo x` is annotated,`grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "The `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "]` attribute is used to annotate declarations."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "!]` attribute is used to annotate declarations, but selecting minimal indexable subterms."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "!\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "!]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_extensionMapRef;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___auto__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(160, 1, 171, 211, 177, 132, 129, 49)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_grindExt;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 161, 226, 116, 111, 153, 146, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "liaExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 224, 62, 90, 13, 174, 224, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liaExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_mkSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx(lean_object* v_x_15_){
_start:
{
switch(lean_obj_tag(v_x_15_))
{
case 0:
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(0u);
return v___x_16_;
}
case 1:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(1u);
return v___x_17_;
}
case 2:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(2u);
return v___x_18_;
}
case 3:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(3u);
return v___x_19_;
}
case 4:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(4u);
return v___x_20_;
}
case 5:
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(5u);
return v___x_21_;
}
case 6:
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(6u);
return v___x_22_;
}
case 7:
{
lean_object* v___x_23_; 
v___x_23_ = lean_unsigned_to_nat(7u);
return v___x_23_;
}
case 8:
{
lean_object* v___x_24_; 
v___x_24_ = lean_unsigned_to_nat(8u);
return v___x_24_;
}
case 9:
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(9u);
return v___x_25_;
}
case 10:
{
lean_object* v___x_26_; 
v___x_26_ = lean_unsigned_to_nat(10u);
return v___x_26_;
}
default: 
{
lean_object* v___x_27_; 
v___x_27_ = lean_unsigned_to_nat(11u);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___boxed(lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_AttrKind_ctorIdx(v_x_28_);
lean_dec(v_x_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_30_, lean_object* v_k_31_){
_start:
{
switch(lean_obj_tag(v_t_30_))
{
case 0:
{
lean_object* v_k_32_; lean_object* v___x_33_; 
v_k_32_ = lean_ctor_get(v_t_30_, 0);
lean_inc(v_k_32_);
lean_dec_ref_known(v_t_30_, 1);
v___x_33_ = lean_apply_1(v_k_31_, v_k_32_);
return v___x_33_;
}
case 1:
{
uint8_t v_eager_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_eager_34_ = lean_ctor_get_uint8(v_t_30_, 0);
lean_dec_ref_known(v_t_30_, 0);
v___x_35_ = lean_box(v_eager_34_);
v___x_36_ = lean_apply_1(v_k_31_, v___x_35_);
return v___x_36_;
}
case 5:
{
lean_object* v_prio_37_; lean_object* v___x_38_; 
v_prio_37_ = lean_ctor_get(v_t_30_, 0);
lean_inc(v_prio_37_);
lean_dec_ref_known(v_t_30_, 1);
v___x_38_ = lean_apply_1(v_k_31_, v_prio_37_);
return v___x_38_;
}
case 8:
{
uint8_t v_post_39_; uint8_t v_inv_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_post_39_ = lean_ctor_get_uint8(v_t_30_, 0);
v_inv_40_ = lean_ctor_get_uint8(v_t_30_, 1);
lean_dec_ref_known(v_t_30_, 0);
v___x_41_ = lean_box(v_post_39_);
v___x_42_ = lean_box(v_inv_40_);
v___x_43_ = lean_apply_2(v_k_31_, v___x_41_, v___x_42_);
return v___x_43_;
}
default: 
{
lean_dec(v_t_30_);
return v_k_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_44_, lean_object* v_ctorIdx_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_k_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_46_, v_k_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_50_, lean_object* v_ctorIdx_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_k_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_50_, v_ctorIdx_51_, v_t_52_, v_h_53_, v_k_54_);
lean_dec(v_ctorIdx_51_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_56_, lean_object* v_ematch_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_56_, v_ematch_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_ematch_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_60_, v_ematch_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_64_, lean_object* v_cases_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_64_, v_cases_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_cases_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_68_, v_cases_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_72_, lean_object* v_intro_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_72_, v_intro_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_intro_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_76_, v_intro_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_80_, lean_object* v_infer_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_80_, v_infer_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_infer_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_84_, v_infer_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_88_, lean_object* v_ext_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_88_, v_ext_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_ext_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_92_, v_ext_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_96_, lean_object* v_symbol_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_96_, v_symbol_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_symbol_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_100_, v_symbol_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_104_, lean_object* v_inj_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_104_, v_inj_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_inj_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_108_, v_inj_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_112_, lean_object* v_funCC_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_112_, v_funCC_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_funCC_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_116_, v_funCC_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_120_, lean_object* v_norm_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_120_, v_norm_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_123_, lean_object* v_t_124_, lean_object* v_h_125_, lean_object* v_norm_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_124_, v_norm_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_128_, lean_object* v_unfold_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_128_, v_unfold_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_unfold_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_132_, v_unfold_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_136_, lean_object* v_homo_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_136_, v_homo_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_homo_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_140_, v_homo_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object* v_t_144_, lean_object* v_homoPred_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_144_, v_homoPred_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object* v_motive_147_, lean_object* v_t_148_, lean_object* v_h_149_, lean_object* v_homoPred_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_148_, v_homoPred_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_152_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
lean_ctor_set(v___x_157_, 3, v___x_156_);
lean_ctor_set(v___x_157_, 4, v___x_155_);
lean_ctor_set(v___x_157_, 5, v___x_155_);
lean_ctor_set(v___x_157_, 6, v___x_155_);
lean_ctor_set(v___x_157_, 7, v___x_155_);
lean_ctor_set(v___x_157_, 8, v___x_155_);
lean_ctor_set(v___x_157_, 9, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(32u);
v___x_159_ = lean_mk_empty_array_with_capacity(v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = ((size_t)5ULL);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_unsigned_to_nat(32u);
v___x_164_ = lean_mk_empty_array_with_capacity(v___x_163_);
v___x_165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_162_);
lean_ctor_set(v___x_166_, 3, v___x_162_);
lean_ctor_set_usize(v___x_166_, 4, v___x_161_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_box(1);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; lean_object* v_env_176_; lean_object* v_options_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_175_ = lean_st_ref_get(v___y_173_);
v_env_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc_ref(v_env_176_);
lean_dec(v___x_175_);
v_options_177_ = lean_ctor_get(v___y_172_, 2);
v___x_178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_177_);
v___x_180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_180_, 0, v_env_176_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
lean_ctor_set(v___x_180_, 3, v_options_177_);
v___x_181_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_msgData_171_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_ref_192_; lean_object* v___x_193_; lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_202_; 
v_ref_192_ = lean_ctor_get(v___y_189_, 5);
v___x_193_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_188_, v___y_189_, v___y_190_);
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_202_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_202_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_202_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
lean_inc(v_ref_192_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v_ref_192_);
lean_ctor_set(v___x_198_, 1, v_a_194_);
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 1);
lean_ctor_set(v___x_196_, 0, v___x_198_);
v___x_200_ = v___x_196_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_208_, lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_fileName_213_; lean_object* v_fileMap_214_; lean_object* v_options_215_; lean_object* v_currRecDepth_216_; lean_object* v_maxRecDepth_217_; lean_object* v_ref_218_; lean_object* v_currNamespace_219_; lean_object* v_openDecls_220_; lean_object* v_initHeartbeats_221_; lean_object* v_maxHeartbeats_222_; lean_object* v_quotContext_223_; lean_object* v_currMacroScope_224_; uint8_t v_diag_225_; lean_object* v_cancelTk_x3f_226_; uint8_t v_suppressElabErrors_227_; lean_object* v_inheritedTraceOptions_228_; lean_object* v_ref_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_fileName_213_ = lean_ctor_get(v___y_210_, 0);
v_fileMap_214_ = lean_ctor_get(v___y_210_, 1);
v_options_215_ = lean_ctor_get(v___y_210_, 2);
v_currRecDepth_216_ = lean_ctor_get(v___y_210_, 3);
v_maxRecDepth_217_ = lean_ctor_get(v___y_210_, 4);
v_ref_218_ = lean_ctor_get(v___y_210_, 5);
v_currNamespace_219_ = lean_ctor_get(v___y_210_, 6);
v_openDecls_220_ = lean_ctor_get(v___y_210_, 7);
v_initHeartbeats_221_ = lean_ctor_get(v___y_210_, 8);
v_maxHeartbeats_222_ = lean_ctor_get(v___y_210_, 9);
v_quotContext_223_ = lean_ctor_get(v___y_210_, 10);
v_currMacroScope_224_ = lean_ctor_get(v___y_210_, 11);
v_diag_225_ = lean_ctor_get_uint8(v___y_210_, sizeof(void*)*14);
v_cancelTk_x3f_226_ = lean_ctor_get(v___y_210_, 12);
v_suppressElabErrors_227_ = lean_ctor_get_uint8(v___y_210_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_228_ = lean_ctor_get(v___y_210_, 13);
v_ref_229_ = l_Lean_replaceRef(v_ref_208_, v_ref_218_);
lean_inc_ref(v_inheritedTraceOptions_228_);
lean_inc(v_cancelTk_x3f_226_);
lean_inc(v_currMacroScope_224_);
lean_inc(v_quotContext_223_);
lean_inc(v_maxHeartbeats_222_);
lean_inc(v_initHeartbeats_221_);
lean_inc(v_openDecls_220_);
lean_inc(v_currNamespace_219_);
lean_inc(v_maxRecDepth_217_);
lean_inc(v_currRecDepth_216_);
lean_inc_ref(v_options_215_);
lean_inc_ref(v_fileMap_214_);
lean_inc_ref(v_fileName_213_);
v___x_230_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_230_, 0, v_fileName_213_);
lean_ctor_set(v___x_230_, 1, v_fileMap_214_);
lean_ctor_set(v___x_230_, 2, v_options_215_);
lean_ctor_set(v___x_230_, 3, v_currRecDepth_216_);
lean_ctor_set(v___x_230_, 4, v_maxRecDepth_217_);
lean_ctor_set(v___x_230_, 5, v_ref_229_);
lean_ctor_set(v___x_230_, 6, v_currNamespace_219_);
lean_ctor_set(v___x_230_, 7, v_openDecls_220_);
lean_ctor_set(v___x_230_, 8, v_initHeartbeats_221_);
lean_ctor_set(v___x_230_, 9, v_maxHeartbeats_222_);
lean_ctor_set(v___x_230_, 10, v_quotContext_223_);
lean_ctor_set(v___x_230_, 11, v_currMacroScope_224_);
lean_ctor_set(v___x_230_, 12, v_cancelTk_x3f_226_);
lean_ctor_set(v___x_230_, 13, v_inheritedTraceOptions_228_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*14, v_diag_225_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*14 + 1, v_suppressElabErrors_227_);
v___x_231_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_209_, v___x_230_, v___y_211_);
lean_dec_ref_known(v___x_230_, 14);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_232_, lean_object* v_msg_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_232_, v_msg_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v_ref_232_);
return v_res_237_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__4));
v___x_248_ = l_Lean_stringToMessageData(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__6));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__53(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__52));
v___x_386_ = l_Lean_stringToMessageData(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
lean_inc(v_stx_414_);
v___x_419_ = l_Lean_Syntax_isOfKind(v_stx_414_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_420_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_421_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_424_, v_a_415_, v_a_416_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = l_Lean_Syntax_getArg(v_stx_414_, v___x_426_);
v___x_428_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__9));
lean_inc(v___x_427_);
v___x_429_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__11));
lean_inc(v___x_427_);
v___x_431_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__13));
lean_inc(v___x_427_);
v___x_433_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__15));
lean_inc(v___x_427_);
v___x_435_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__17));
lean_inc(v___x_427_);
v___x_437_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__19));
lean_inc(v___x_427_);
v___x_439_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__21));
lean_inc(v___x_427_);
v___x_441_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__23));
lean_inc(v___x_427_);
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__25));
lean_inc(v___x_427_);
v___x_445_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__27));
lean_inc(v___x_427_);
v___x_447_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
lean_inc(v___x_427_);
v___x_449_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__31));
lean_inc(v___x_427_);
v___x_451_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__33));
lean_inc(v___x_427_);
v___x_453_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__35));
lean_inc(v___x_427_);
v___x_455_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__37));
lean_inc(v___x_427_);
v___x_457_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__39));
lean_inc(v___x_427_);
v___x_459_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__41));
lean_inc(v___x_427_);
v___x_461_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__43));
lean_inc(v___x_427_);
v___x_463_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__45));
lean_inc(v___x_427_);
v___x_465_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__47));
lean_inc(v___x_427_);
v___x_467_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__49));
lean_inc(v___x_427_);
v___x_469_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__51));
lean_inc(v___x_427_);
v___x_471_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v___x_427_);
v___x_472_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_473_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_476_, v_a_415_, v_a_416_);
return v___x_477_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v_stx_414_);
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = l_Lean_Syntax_getArg(v___x_427_, v___x_478_);
lean_dec(v___x_427_);
v___x_480_ = l_Lean_Syntax_isNatLit_x3f(v___x_479_);
if (lean_obj_tag(v___x_480_) == 1)
{
lean_object* v_val_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
lean_dec(v___x_479_);
v_val_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_489_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_val_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 5);
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_val_481_);
v___x_486_ = v_reuseFailAlloc_488_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; 
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v___x_480_);
v___x_490_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__53, &l_Lean_Meta_Grind_getAttrKindCore___closed__53_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__53);
v___x_491_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_479_, v___x_490_, v_a_415_, v_a_416_);
lean_dec(v___x_479_);
return v___x_491_;
}
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_492_ = lean_box(11);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_494_ = lean_box(10);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_496_ = lean_box(9);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = l_Lean_Syntax_getArg(v___x_427_, v___x_498_);
lean_inc(v___x_499_);
v___x_500_ = l_Lean_Syntax_matchesNull(v___x_499_, v___x_426_);
if (v___x_500_ == 0)
{
uint8_t v___x_501_; 
lean_inc(v___x_499_);
v___x_501_ = l_Lean_Syntax_matchesNull(v___x_499_, v___x_498_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v___x_499_);
lean_dec(v___x_427_);
v___x_502_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_503_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_506_, v_a_415_, v_a_416_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_508_ = l_Lean_Syntax_getArg(v___x_499_, v___x_426_);
lean_dec(v___x_499_);
v___x_509_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
lean_inc(v___x_508_);
v___x_510_ = l_Lean_Syntax_isOfKind(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
v___x_512_ = l_Lean_Syntax_isOfKind(v___x_508_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v___x_427_);
v___x_513_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_514_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_517_, v_a_415_, v_a_416_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_unsigned_to_nat(2u);
v___x_520_ = l_Lean_Syntax_getArg(v___x_427_, v___x_519_);
lean_dec(v___x_427_);
lean_inc(v___x_520_);
v___x_521_ = l_Lean_Syntax_matchesNull(v___x_520_, v___x_426_);
if (v___x_521_ == 0)
{
uint8_t v___x_522_; 
v___x_522_ = l_Lean_Syntax_matchesNull(v___x_520_, v___x_498_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_523_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_524_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_527_, v_a_415_, v_a_416_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_stx_414_);
v___x_529_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_529_, 0, v___x_521_);
lean_ctor_set_uint8(v___x_529_, 1, v___x_419_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v___x_520_);
lean_dec(v_stx_414_);
v___x_531_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_531_, 0, v___x_510_);
lean_ctor_set_uint8(v___x_531_, 1, v___x_510_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
lean_dec(v___x_508_);
v___x_533_ = lean_unsigned_to_nat(2u);
v___x_534_ = l_Lean_Syntax_getArg(v___x_427_, v___x_533_);
lean_dec(v___x_427_);
lean_inc(v___x_534_);
v___x_535_ = l_Lean_Syntax_matchesNull(v___x_534_, v___x_426_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; 
v___x_536_ = l_Lean_Syntax_matchesNull(v___x_534_, v___x_498_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_537_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_538_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_541_, v_a_415_, v_a_416_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec(v_stx_414_);
v___x_543_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_543_, 0, v___x_419_);
lean_ctor_set_uint8(v___x_543_, 1, v___x_419_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v___x_534_);
lean_dec(v_stx_414_);
v___x_545_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_545_, 0, v___x_419_);
lean_ctor_set_uint8(v___x_545_, 1, v___x_500_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
}
}
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
lean_dec(v___x_499_);
v___x_547_ = lean_unsigned_to_nat(2u);
v___x_548_ = l_Lean_Syntax_getArg(v___x_427_, v___x_547_);
lean_dec(v___x_427_);
lean_inc(v___x_548_);
v___x_549_ = l_Lean_Syntax_matchesNull(v___x_548_, v___x_426_);
if (v___x_549_ == 0)
{
uint8_t v___x_550_; 
v___x_550_ = l_Lean_Syntax_matchesNull(v___x_548_, v___x_498_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_551_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_552_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_555_, v_a_415_, v_a_416_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v_stx_414_);
v___x_557_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_557_, 0, v___x_419_);
lean_ctor_set_uint8(v___x_557_, 1, v___x_419_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v___x_548_);
lean_dec(v_stx_414_);
v___x_559_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_559_, 0, v___x_419_);
lean_ctor_set_uint8(v___x_559_, 1, v___x_461_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_561_ = lean_box(7);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_563_ = lean_box(6);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_565_ = lean_box(4);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_567_ = lean_box(2);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_569_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_569_, 0, v___x_419_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_571_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_571_, 0, v___x_449_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_573_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_573_, 0, v___x_419_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_576_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__59));
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_578_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_580_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_582_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_584_ = lean_unsigned_to_nat(3u);
v___x_585_ = l_Lean_Syntax_getArg(v___x_427_, v___x_584_);
lean_dec(v___x_427_);
lean_inc(v___x_585_);
v___x_586_ = l_Lean_Syntax_matchesNull(v___x_585_, v___x_426_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_585_);
v___x_588_ = l_Lean_Syntax_matchesNull(v___x_585_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v___x_585_);
v___x_589_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_590_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_593_, v_a_415_, v_a_416_);
return v___x_594_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_595_ = l_Lean_Syntax_getArg(v___x_585_, v___x_426_);
lean_dec(v___x_585_);
v___x_596_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_597_ = l_Lean_Syntax_isOfKind(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_598_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_599_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_602_, v_a_415_, v_a_416_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_stx_414_);
v___x_604_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_604_, 0, v___x_419_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v___x_585_);
lean_dec(v_stx_414_);
v___x_607_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_607_, 0, v___x_437_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_unsigned_to_nat(2u);
v___x_611_ = l_Lean_Syntax_getArg(v___x_427_, v___x_610_);
lean_dec(v___x_427_);
lean_inc(v___x_611_);
v___x_612_ = l_Lean_Syntax_matchesNull(v___x_611_, v___x_426_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_611_);
v___x_614_ = l_Lean_Syntax_matchesNull(v___x_611_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v___x_611_);
v___x_615_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_616_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_619_, v_a_415_, v_a_416_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = l_Lean_Syntax_getArg(v___x_611_, v___x_426_);
lean_dec(v___x_611_);
v___x_622_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_623_ = l_Lean_Syntax_isOfKind(v___x_621_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_624_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_625_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_628_, v_a_415_, v_a_416_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v_stx_414_);
v___x_630_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_630_, 0, v___x_419_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec(v___x_611_);
lean_dec(v_stx_414_);
v___x_633_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_633_, 0, v___x_435_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = l_Lean_Syntax_getArg(v___x_427_, v___x_636_);
lean_dec(v___x_427_);
lean_inc(v___x_637_);
v___x_638_ = l_Lean_Syntax_matchesNull(v___x_637_, v___x_426_);
if (v___x_638_ == 0)
{
uint8_t v___x_639_; 
lean_inc(v___x_637_);
v___x_639_ = l_Lean_Syntax_matchesNull(v___x_637_, v___x_636_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v___x_637_);
v___x_640_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_641_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_644_, v_a_415_, v_a_416_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = l_Lean_Syntax_getArg(v___x_637_, v___x_426_);
lean_dec(v___x_637_);
v___x_647_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_648_ = l_Lean_Syntax_isOfKind(v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_649_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_650_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_653_, v_a_415_, v_a_416_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v_stx_414_);
v___x_655_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_655_, 0, v___x_419_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec(v___x_637_);
lean_dec(v_stx_414_);
v___x_658_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_658_, 0, v___x_433_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_661_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = l_Lean_Syntax_getArg(v___x_427_, v___x_663_);
lean_dec(v___x_427_);
lean_inc(v___x_664_);
v___x_665_ = l_Lean_Syntax_matchesNull(v___x_664_, v___x_426_);
if (v___x_665_ == 0)
{
uint8_t v___x_666_; 
lean_inc(v___x_664_);
v___x_666_ = l_Lean_Syntax_matchesNull(v___x_664_, v___x_663_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v___x_664_);
v___x_667_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_668_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_671_, v_a_415_, v_a_416_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_673_ = l_Lean_Syntax_getArg(v___x_664_, v___x_426_);
lean_dec(v___x_664_);
v___x_674_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_675_ = l_Lean_Syntax_isOfKind(v___x_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_676_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_677_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_680_, v_a_415_, v_a_416_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v_stx_414_);
v___x_682_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_682_, 0, v___x_419_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v___x_664_);
lean_dec(v_stx_414_);
v___x_685_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_685_, 0, v___x_429_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = l_Lean_Syntax_getArg(v___x_427_, v___x_688_);
lean_dec(v___x_427_);
lean_inc(v___x_689_);
v___x_690_ = l_Lean_Syntax_matchesNull(v___x_689_, v___x_426_);
if (v___x_690_ == 0)
{
uint8_t v___x_691_; 
lean_inc(v___x_689_);
v___x_691_ = l_Lean_Syntax_matchesNull(v___x_689_, v___x_688_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v___x_689_);
v___x_692_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_693_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_696_, v_a_415_, v_a_416_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_698_ = l_Lean_Syntax_getArg(v___x_689_, v___x_426_);
lean_dec(v___x_689_);
v___x_699_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_700_ = l_Lean_Syntax_isOfKind(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_701_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_702_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_705_, v_a_415_, v_a_416_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v_stx_414_);
v___x_707_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_707_, 0, v___x_419_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec(v___x_689_);
lean_dec(v_stx_414_);
v___x_710_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_712_, v_a_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_717_, lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_718_, v___y_719_, v___y_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_723_, lean_object* v_msg_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_723_, v_msg_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_729_, lean_object* v_ref_730_, lean_object* v_msg_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_730_, v_msg_731_, v___y_732_, v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_736_, lean_object* v_ref_737_, lean_object* v_msg_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_736_, v_ref_737_, v_msg_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v_ref_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = l_Lean_Syntax_getArg(v_stx_743_, v___x_747_);
v___x_749_ = l_Lean_Syntax_isNone(v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = l_Lean_Syntax_getArg(v___x_748_, v___x_750_);
lean_dec(v___x_748_);
v___x_752_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_751_, v_a_744_, v_a_745_);
return v___x_752_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v___x_748_);
v___x_753_ = lean_box(3);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_stx_755_);
return v_res_759_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_762_ = l_Lean_stringToMessageData(v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_767_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_766_, v_a_763_, v_a_764_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_773_, v_a_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_777_, v_a_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
return v_res_781_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_782_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_787_, lean_object* v_b_788_, uint8_t v_kind_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_currNamespace_793_; lean_object* v___x_794_; lean_object* v_env_795_; lean_object* v_nextMacroScope_796_; lean_object* v_ngen_797_; lean_object* v_auxDeclNGen_798_; lean_object* v_traceState_799_; lean_object* v_messages_800_; lean_object* v_infoState_801_; lean_object* v_snapshotTasks_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_814_; 
v_currNamespace_793_ = lean_ctor_get(v___y_790_, 6);
v___x_794_ = lean_st_ref_take(v___y_791_);
v_env_795_ = lean_ctor_get(v___x_794_, 0);
v_nextMacroScope_796_ = lean_ctor_get(v___x_794_, 1);
v_ngen_797_ = lean_ctor_get(v___x_794_, 2);
v_auxDeclNGen_798_ = lean_ctor_get(v___x_794_, 3);
v_traceState_799_ = lean_ctor_get(v___x_794_, 4);
v_messages_800_ = lean_ctor_get(v___x_794_, 6);
v_infoState_801_ = lean_ctor_get(v___x_794_, 7);
v_snapshotTasks_802_ = lean_ctor_get(v___x_794_, 8);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v___x_794_, 5);
lean_dec(v_unused_815_);
v___x_804_ = v___x_794_;
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_snapshotTasks_802_);
lean_inc(v_infoState_801_);
lean_inc(v_messages_800_);
lean_inc(v_traceState_799_);
lean_inc(v_auxDeclNGen_798_);
lean_inc(v_ngen_797_);
lean_inc(v_nextMacroScope_796_);
lean_inc(v_env_795_);
lean_dec(v___x_794_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
lean_inc(v_currNamespace_793_);
v___x_806_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_795_, v_ext_787_, v_b_788_, v_kind_789_, v_currNamespace_793_);
v___x_807_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 5, v___x_807_);
lean_ctor_set(v___x_804_, 0, v___x_806_);
v___x_809_ = v___x_804_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_nextMacroScope_796_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_ngen_797_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_auxDeclNGen_798_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_traceState_799_);
lean_ctor_set(v_reuseFailAlloc_813_, 5, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_813_, 6, v_messages_800_);
lean_ctor_set(v_reuseFailAlloc_813_, 7, v_infoState_801_);
lean_ctor_set(v_reuseFailAlloc_813_, 8, v_snapshotTasks_802_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_810_ = lean_st_ref_set(v___y_791_, v___x_809_);
v___x_811_ = lean_box(0);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_816_, lean_object* v_b_817_, lean_object* v_kind_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
uint8_t v_kind_boxed_822_; lean_object* v_res_823_; 
v_kind_boxed_822_ = lean_unbox(v_kind_818_);
v_res_823_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_816_, v_b_817_, v_kind_boxed_822_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_00_u03c3_826_, lean_object* v_ext_827_, lean_object* v_b_828_, uint8_t v_kind_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_827_, v_b_828_, v_kind_829_, v___y_830_, v___y_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_834_, lean_object* v_00_u03b2_835_, lean_object* v_00_u03c3_836_, lean_object* v_ext_837_, lean_object* v_b_838_, lean_object* v_kind_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
uint8_t v_kind_boxed_843_; lean_object* v_res_844_; 
v_kind_boxed_843_ = lean_unbox(v_kind_839_);
v_res_844_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_834_, v_00_u03b2_835_, v_00_u03c3_836_, v_ext_837_, v_b_838_, v_kind_boxed_843_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_845_, lean_object* v_declName_846_, uint8_t v_eager_847_, uint8_t v_attrKind_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v___x_852_; 
lean_inc(v_declName_846_);
v___x_852_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_846_, v_eager_847_, v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec_ref_known(v___x_852_, 1);
v___x_853_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_853_, 0, v_declName_846_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*1, v_eager_847_);
v___x_854_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_845_, v___x_853_, v_attrKind_848_, v_a_849_, v_a_850_);
return v___x_854_;
}
else
{
lean_dec(v_declName_846_);
lean_dec_ref(v_ext_845_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_855_, lean_object* v_declName_856_, lean_object* v_eager_857_, lean_object* v_attrKind_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
uint8_t v_eager_boxed_862_; uint8_t v_attrKind_boxed_863_; lean_object* v_res_864_; 
v_eager_boxed_862_ = lean_unbox(v_eager_857_);
v_attrKind_boxed_863_ = lean_unbox(v_attrKind_858_);
v_res_864_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_855_, v_declName_856_, v_eager_boxed_862_, v_attrKind_boxed_863_, v_a_859_, v_a_860_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_865_, lean_object* v_declName_866_, uint8_t v_attrKind_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_871_; 
lean_inc(v_declName_866_);
v___x_871_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_866_, v_a_868_, v_a_869_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_879_; 
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v___x_871_, 0);
lean_dec(v_unused_880_);
v___x_873_ = v___x_871_;
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
else
{
lean_dec(v___x_871_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v_declName_866_);
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_declName_866_);
v___x_876_ = v_reuseFailAlloc_878_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_865_, v___x_876_, v_attrKind_867_, v_a_868_, v_a_869_);
return v___x_877_;
}
}
}
else
{
lean_dec(v_declName_866_);
lean_dec_ref(v_ext_865_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_881_, lean_object* v_declName_882_, lean_object* v_attrKind_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
uint8_t v_attrKind_boxed_887_; lean_object* v_res_888_; 
v_attrKind_boxed_887_ = lean_unbox(v_attrKind_883_);
v_res_888_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_881_, v_declName_882_, v_attrKind_boxed_887_, v_a_884_, v_a_885_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_889_, lean_object* v_declName_890_, uint8_t v_attrKind_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v_declName_890_);
v___x_896_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_889_, v___x_895_, v_attrKind_891_, v_a_892_, v_a_893_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_897_, lean_object* v_declName_898_, lean_object* v_attrKind_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
uint8_t v_attrKind_boxed_903_; lean_object* v_res_904_; 
v_attrKind_boxed_903_ = lean_unbox(v_attrKind_899_);
v_res_904_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_897_, v_declName_898_, v_attrKind_boxed_903_, v_a_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_905_, lean_object* v_s_906_){
_start:
{
lean_object* v_casesTypes_907_; lean_object* v_funCC_908_; lean_object* v_ematch_909_; lean_object* v_inj_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
v_casesTypes_907_ = lean_ctor_get(v_s_906_, 0);
v_funCC_908_ = lean_ctor_get(v_s_906_, 2);
v_ematch_909_ = lean_ctor_get(v_s_906_, 3);
v_inj_910_ = lean_ctor_get(v_s_906_, 4);
v_isSharedCheck_917_ = !lean_is_exclusive(v_s_906_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v_s_906_, 1);
lean_dec(v_unused_918_);
v___x_912_ = v_s_906_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_inj_910_);
lean_inc(v_ematch_909_);
lean_inc(v_funCC_908_);
lean_inc(v_casesTypes_907_);
lean_dec(v_s_906_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_a_905_);
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_casesTypes_907_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_a_905_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_funCC_908_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_ematch_909_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_inj_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_919_, lean_object* v_declName_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_924_; lean_object* v_ext_925_; lean_object* v_toEnvExtension_926_; lean_object* v_env_927_; lean_object* v_asyncMode_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_extThms_931_; lean_object* v___x_932_; 
v___x_924_ = lean_st_ref_get(v_a_922_);
v_ext_925_ = lean_ctor_get(v_ext_919_, 1);
v_toEnvExtension_926_ = lean_ctor_get(v_ext_925_, 0);
v_env_927_ = lean_ctor_get(v___x_924_, 0);
lean_inc_ref(v_env_927_);
lean_dec(v___x_924_);
v_asyncMode_928_ = lean_ctor_get(v_toEnvExtension_926_, 2);
v___x_929_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_930_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_929_, v_ext_919_, v_env_927_, v_asyncMode_928_);
v_extThms_931_ = lean_ctor_get(v___x_930_, 1);
lean_inc_ref(v_extThms_931_);
lean_dec(v___x_930_);
v___x_932_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_931_, v_declName_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_962_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_962_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_962_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_962_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v_env_938_; lean_object* v_nextMacroScope_939_; lean_object* v_ngen_940_; lean_object* v_auxDeclNGen_941_; lean_object* v_traceState_942_; lean_object* v_messages_943_; lean_object* v_infoState_944_; lean_object* v_snapshotTasks_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_960_; 
v___x_937_ = lean_st_ref_take(v_a_922_);
v_env_938_ = lean_ctor_get(v___x_937_, 0);
v_nextMacroScope_939_ = lean_ctor_get(v___x_937_, 1);
v_ngen_940_ = lean_ctor_get(v___x_937_, 2);
v_auxDeclNGen_941_ = lean_ctor_get(v___x_937_, 3);
v_traceState_942_ = lean_ctor_get(v___x_937_, 4);
v_messages_943_ = lean_ctor_get(v___x_937_, 6);
v_infoState_944_ = lean_ctor_get(v___x_937_, 7);
v_snapshotTasks_945_ = lean_ctor_get(v___x_937_, 8);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v___x_937_, 5);
lean_dec(v_unused_961_);
v___x_947_ = v___x_937_;
v_isShared_948_ = v_isSharedCheck_960_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snapshotTasks_945_);
lean_inc(v_infoState_944_);
lean_inc(v_messages_943_);
lean_inc(v_traceState_942_);
lean_inc(v_auxDeclNGen_941_);
lean_inc(v_ngen_940_);
lean_inc(v_nextMacroScope_939_);
lean_inc(v_env_938_);
lean_dec(v___x_937_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_960_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___f_949_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_949_, 0, v_a_933_);
v___x_950_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_919_, v_env_938_, v___f_949_);
v___x_951_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 5, v___x_951_);
lean_ctor_set(v___x_947_, 0, v___x_950_);
v___x_953_ = v___x_947_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_nextMacroScope_939_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_ngen_940_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_auxDeclNGen_941_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_traceState_942_);
lean_ctor_set(v_reuseFailAlloc_959_, 5, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_959_, 6, v_messages_943_);
lean_ctor_set(v_reuseFailAlloc_959_, 7, v_infoState_944_);
lean_ctor_set(v_reuseFailAlloc_959_, 8, v_snapshotTasks_945_);
v___x_953_ = v_reuseFailAlloc_959_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_954_ = lean_st_ref_set(v_a_922_, v___x_953_);
v___x_955_ = lean_box(0);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_955_);
v___x_957_ = v___x_935_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec_ref(v_ext_919_);
v_a_963_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_932_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_932_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_971_, lean_object* v_declName_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_971_, v_declName_972_, v_a_973_, v_a_974_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_977_, lean_object* v_s_978_){
_start:
{
lean_object* v_extThms_979_; lean_object* v_funCC_980_; lean_object* v_ematch_981_; lean_object* v_inj_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_extThms_979_ = lean_ctor_get(v_s_978_, 1);
v_funCC_980_ = lean_ctor_get(v_s_978_, 2);
v_ematch_981_ = lean_ctor_get(v_s_978_, 3);
v_inj_982_ = lean_ctor_get(v_s_978_, 4);
v_isSharedCheck_989_ = !lean_is_exclusive(v_s_978_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v_s_978_, 0);
lean_dec(v_unused_990_);
v___x_984_ = v_s_978_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_inj_982_);
lean_inc(v_ematch_981_);
lean_inc(v_funCC_980_);
lean_inc(v_extThms_979_);
lean_dec(v_s_978_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v_a_977_);
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_977_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_extThms_979_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v_funCC_980_);
lean_ctor_set(v_reuseFailAlloc_988_, 3, v_ematch_981_);
lean_ctor_set(v_reuseFailAlloc_988_, 4, v_inj_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_991_, lean_object* v_declName_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_996_; 
lean_inc(v_declName_992_);
v___x_996_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_997_; lean_object* v_ext_998_; lean_object* v_toEnvExtension_999_; lean_object* v_env_1000_; lean_object* v_asyncMode_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v_casesTypes_1004_; lean_object* v___x_1005_; 
lean_dec_ref_known(v___x_996_, 1);
v___x_997_ = lean_st_ref_get(v_a_994_);
v_ext_998_ = lean_ctor_get(v_ext_991_, 1);
v_toEnvExtension_999_ = lean_ctor_get(v_ext_998_, 0);
v_env_1000_ = lean_ctor_get(v___x_997_, 0);
lean_inc_ref(v_env_1000_);
lean_dec(v___x_997_);
v_asyncMode_1001_ = lean_ctor_get(v_toEnvExtension_999_, 2);
v___x_1002_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1003_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1002_, v_ext_991_, v_env_1000_, v_asyncMode_1001_);
v_casesTypes_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc_ref(v_casesTypes_1004_);
lean_dec(v___x_1003_);
v___x_1005_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_1004_, v_declName_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1035_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1035_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1035_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v_env_1011_; lean_object* v_nextMacroScope_1012_; lean_object* v_ngen_1013_; lean_object* v_auxDeclNGen_1014_; lean_object* v_traceState_1015_; lean_object* v_messages_1016_; lean_object* v_infoState_1017_; lean_object* v_snapshotTasks_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1033_; 
v___x_1010_ = lean_st_ref_take(v_a_994_);
v_env_1011_ = lean_ctor_get(v___x_1010_, 0);
v_nextMacroScope_1012_ = lean_ctor_get(v___x_1010_, 1);
v_ngen_1013_ = lean_ctor_get(v___x_1010_, 2);
v_auxDeclNGen_1014_ = lean_ctor_get(v___x_1010_, 3);
v_traceState_1015_ = lean_ctor_get(v___x_1010_, 4);
v_messages_1016_ = lean_ctor_get(v___x_1010_, 6);
v_infoState_1017_ = lean_ctor_get(v___x_1010_, 7);
v_snapshotTasks_1018_ = lean_ctor_get(v___x_1010_, 8);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v___x_1010_, 5);
lean_dec(v_unused_1034_);
v___x_1020_ = v___x_1010_;
v_isShared_1021_ = v_isSharedCheck_1033_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_snapshotTasks_1018_);
lean_inc(v_infoState_1017_);
lean_inc(v_messages_1016_);
lean_inc(v_traceState_1015_);
lean_inc(v_auxDeclNGen_1014_);
lean_inc(v_ngen_1013_);
lean_inc(v_nextMacroScope_1012_);
lean_inc(v_env_1011_);
lean_dec(v___x_1010_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1033_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___f_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___f_1022_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_1022_, 0, v_a_1006_);
v___x_1023_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_991_, v_env_1011_, v___f_1022_);
v___x_1024_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 5, v___x_1024_);
lean_ctor_set(v___x_1020_, 0, v___x_1023_);
v___x_1026_ = v___x_1020_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_nextMacroScope_1012_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_ngen_1013_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_auxDeclNGen_1014_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v_traceState_1015_);
lean_ctor_set(v_reuseFailAlloc_1032_, 5, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1032_, 6, v_messages_1016_);
lean_ctor_set(v_reuseFailAlloc_1032_, 7, v_infoState_1017_);
lean_ctor_set(v_reuseFailAlloc_1032_, 8, v_snapshotTasks_1018_);
v___x_1026_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1027_ = lean_st_ref_set(v_a_994_, v___x_1026_);
v___x_1028_ = lean_box(0);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1028_);
v___x_1030_ = v___x_1008_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec_ref(v_ext_991_);
v_a_1036_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1005_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1005_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_dec(v_declName_992_);
lean_dec_ref(v_ext_991_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_1044_, lean_object* v_declName_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1044_, v_declName_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_1050_, lean_object* v_s_1051_){
_start:
{
lean_object* v_casesTypes_1052_; lean_object* v_extThms_1053_; lean_object* v_ematch_1054_; lean_object* v_inj_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_casesTypes_1052_ = lean_ctor_get(v_s_1051_, 0);
v_extThms_1053_ = lean_ctor_get(v_s_1051_, 1);
v_ematch_1054_ = lean_ctor_get(v_s_1051_, 3);
v_inj_1055_ = lean_ctor_get(v_s_1051_, 4);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_s_1051_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; 
v_unused_1063_ = lean_ctor_get(v_s_1051_, 2);
lean_dec(v_unused_1063_);
v___x_1057_ = v_s_1051_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_inj_1055_);
lean_inc(v_ematch_1054_);
lean_inc(v_extThms_1053_);
lean_inc(v_casesTypes_1052_);
lean_dec(v_s_1051_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 2, v___x_1050_);
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_casesTypes_1052_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_extThms_1053_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1061_, 3, v_ematch_1054_);
lean_ctor_set(v_reuseFailAlloc_1061_, 4, v_inj_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_1064_, lean_object* v_t_1065_){
_start:
{
if (lean_obj_tag(v_t_1065_) == 0)
{
lean_object* v_k_1066_; lean_object* v_v_1067_; lean_object* v_l_1068_; lean_object* v_r_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1723_; 
v_k_1066_ = lean_ctor_get(v_t_1065_, 1);
v_v_1067_ = lean_ctor_get(v_t_1065_, 2);
v_l_1068_ = lean_ctor_get(v_t_1065_, 3);
v_r_1069_ = lean_ctor_get(v_t_1065_, 4);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_t_1065_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v_t_1065_, 0);
lean_dec(v_unused_1724_);
v___x_1071_ = v_t_1065_;
v_isShared_1072_ = v_isSharedCheck_1723_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_r_1069_);
lean_inc(v_l_1068_);
lean_inc(v_v_1067_);
lean_inc(v_k_1066_);
lean_dec(v_t_1065_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1723_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
uint8_t v___x_1073_; 
v___x_1073_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1064_, v_k_1066_);
switch(v___x_1073_)
{
case 0:
{
lean_object* v_impl_1074_; lean_object* v___x_1075_; 
v_impl_1074_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1064_, v_l_1068_);
v___x_1075_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1074_) == 0)
{
if (lean_obj_tag(v_r_1069_) == 0)
{
lean_object* v_size_1076_; lean_object* v_size_1077_; lean_object* v_k_1078_; lean_object* v_v_1079_; lean_object* v_l_1080_; lean_object* v_r_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v_size_1076_ = lean_ctor_get(v_impl_1074_, 0);
lean_inc(v_size_1076_);
v_size_1077_ = lean_ctor_get(v_r_1069_, 0);
v_k_1078_ = lean_ctor_get(v_r_1069_, 1);
v_v_1079_ = lean_ctor_get(v_r_1069_, 2);
v_l_1080_ = lean_ctor_get(v_r_1069_, 3);
lean_inc(v_l_1080_);
v_r_1081_ = lean_ctor_get(v_r_1069_, 4);
v___x_1082_ = lean_unsigned_to_nat(3u);
v___x_1083_ = lean_nat_mul(v___x_1082_, v_size_1076_);
v___x_1084_ = lean_nat_dec_lt(v___x_1083_, v_size_1077_);
lean_dec(v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
lean_dec(v_l_1080_);
v___x_1085_ = lean_nat_add(v___x_1075_, v_size_1076_);
lean_dec(v_size_1076_);
v___x_1086_ = lean_nat_add(v___x_1085_, v_size_1077_);
lean_dec(v___x_1085_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 3, v_impl_1074_);
lean_ctor_set(v___x_1071_, 0, v___x_1086_);
v___x_1088_ = v___x_1071_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_impl_1074_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_r_1069_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
else
{
lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1153_; 
lean_inc(v_r_1081_);
lean_inc(v_v_1079_);
lean_inc(v_k_1078_);
lean_inc(v_size_1077_);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_r_1069_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; lean_object* v_unused_1155_; lean_object* v_unused_1156_; lean_object* v_unused_1157_; lean_object* v_unused_1158_; 
v_unused_1154_ = lean_ctor_get(v_r_1069_, 4);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v_r_1069_, 3);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_r_1069_, 2);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_r_1069_, 1);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v_r_1069_, 0);
lean_dec(v_unused_1158_);
v___x_1091_ = v_r_1069_;
v_isShared_1092_ = v_isSharedCheck_1153_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v_r_1069_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1153_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_size_1093_; lean_object* v_k_1094_; lean_object* v_v_1095_; lean_object* v_l_1096_; lean_object* v_r_1097_; lean_object* v_size_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_size_1093_ = lean_ctor_get(v_l_1080_, 0);
v_k_1094_ = lean_ctor_get(v_l_1080_, 1);
v_v_1095_ = lean_ctor_get(v_l_1080_, 2);
v_l_1096_ = lean_ctor_get(v_l_1080_, 3);
v_r_1097_ = lean_ctor_get(v_l_1080_, 4);
v_size_1098_ = lean_ctor_get(v_r_1081_, 0);
v___x_1099_ = lean_unsigned_to_nat(2u);
v___x_1100_ = lean_nat_mul(v___x_1099_, v_size_1098_);
v___x_1101_ = lean_nat_dec_lt(v_size_1093_, v___x_1100_);
lean_dec(v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1129_; 
lean_inc(v_r_1097_);
lean_inc(v_l_1096_);
lean_inc(v_v_1095_);
lean_inc(v_k_1094_);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_l_1080_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; lean_object* v_unused_1131_; lean_object* v_unused_1132_; lean_object* v_unused_1133_; lean_object* v_unused_1134_; 
v_unused_1130_ = lean_ctor_get(v_l_1080_, 4);
lean_dec(v_unused_1130_);
v_unused_1131_ = lean_ctor_get(v_l_1080_, 3);
lean_dec(v_unused_1131_);
v_unused_1132_ = lean_ctor_get(v_l_1080_, 2);
lean_dec(v_unused_1132_);
v_unused_1133_ = lean_ctor_get(v_l_1080_, 1);
lean_dec(v_unused_1133_);
v_unused_1134_ = lean_ctor_get(v_l_1080_, 0);
lean_dec(v_unused_1134_);
v___x_1103_ = v_l_1080_;
v_isShared_1104_ = v_isSharedCheck_1129_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v_l_1080_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1129_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1119_; 
v___x_1105_ = lean_nat_add(v___x_1075_, v_size_1076_);
lean_dec(v_size_1076_);
v___x_1106_ = lean_nat_add(v___x_1105_, v_size_1077_);
lean_dec(v_size_1077_);
if (lean_obj_tag(v_l_1096_) == 0)
{
lean_object* v_size_1127_; 
v_size_1127_ = lean_ctor_get(v_l_1096_, 0);
lean_inc(v_size_1127_);
v___y_1119_ = v_size_1127_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_unsigned_to_nat(0u);
v___y_1119_ = v___x_1128_;
goto v___jp_1118_;
}
v___jp_1107_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = lean_nat_add(v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec(v___y_1109_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v_r_1081_);
lean_ctor_set(v___x_1103_, 3, v_r_1097_);
lean_ctor_set(v___x_1103_, 2, v_v_1079_);
lean_ctor_set(v___x_1103_, 1, v_k_1078_);
lean_ctor_set(v___x_1103_, 0, v___x_1111_);
v___x_1113_ = v___x_1103_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_k_1078_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_v_1079_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_r_1097_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v_r_1081_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v___x_1113_);
lean_ctor_set(v___x_1091_, 3, v___y_1108_);
lean_ctor_set(v___x_1091_, 2, v_v_1095_);
lean_ctor_set(v___x_1091_, 1, v_k_1094_);
lean_ctor_set(v___x_1091_, 0, v___x_1106_);
v___x_1115_ = v___x_1091_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_k_1094_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_v_1095_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v___y_1108_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
v___jp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = lean_nat_add(v___x_1105_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec(v___x_1105_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v_l_1096_);
lean_ctor_set(v___x_1071_, 3, v_impl_1074_);
lean_ctor_set(v___x_1071_, 0, v___x_1120_);
v___x_1122_ = v___x_1071_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_impl_1074_);
lean_ctor_set(v_reuseFailAlloc_1126_, 4, v_l_1096_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_nat_add(v___x_1075_, v_size_1098_);
if (lean_obj_tag(v_r_1097_) == 0)
{
lean_object* v_size_1124_; 
v_size_1124_ = lean_ctor_get(v_r_1097_, 0);
lean_inc(v_size_1124_);
v___y_1108_ = v___x_1122_;
v___y_1109_ = v___x_1123_;
v___y_1110_ = v_size_1124_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_unsigned_to_nat(0u);
v___y_1108_ = v___x_1122_;
v___y_1109_ = v___x_1123_;
v___y_1110_ = v___x_1125_;
goto v___jp_1107_;
}
}
}
}
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_del_object(v___x_1071_);
v___x_1135_ = lean_nat_add(v___x_1075_, v_size_1076_);
lean_dec(v_size_1076_);
v___x_1136_ = lean_nat_add(v___x_1135_, v_size_1077_);
lean_dec(v_size_1077_);
v___x_1137_ = lean_nat_add(v___x_1135_, v_size_1093_);
lean_dec(v___x_1135_);
lean_inc_ref(v_impl_1074_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v_l_1080_);
lean_ctor_set(v___x_1091_, 3, v_impl_1074_);
lean_ctor_set(v___x_1091_, 2, v_v_1067_);
lean_ctor_set(v___x_1091_, 1, v_k_1066_);
lean_ctor_set(v___x_1091_, 0, v___x_1137_);
v___x_1139_ = v___x_1091_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_impl_1074_);
lean_ctor_set(v_reuseFailAlloc_1152_, 4, v_l_1080_);
v___x_1139_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_isSharedCheck_1146_ = !lean_is_exclusive(v_impl_1074_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; lean_object* v_unused_1148_; lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; 
v_unused_1147_ = lean_ctor_get(v_impl_1074_, 4);
lean_dec(v_unused_1147_);
v_unused_1148_ = lean_ctor_get(v_impl_1074_, 3);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_impl_1074_, 2);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_impl_1074_, 1);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_impl_1074_, 0);
lean_dec(v_unused_1151_);
v___x_1141_ = v_impl_1074_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v_impl_1074_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 4, v_r_1081_);
lean_ctor_set(v___x_1141_, 3, v___x_1139_);
lean_ctor_set(v___x_1141_, 2, v_v_1079_);
lean_ctor_set(v___x_1141_, 1, v_k_1078_);
lean_ctor_set(v___x_1141_, 0, v___x_1136_);
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_k_1078_);
lean_ctor_set(v_reuseFailAlloc_1145_, 2, v_v_1079_);
lean_ctor_set(v_reuseFailAlloc_1145_, 3, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1145_, 4, v_r_1081_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
v_size_1159_ = lean_ctor_get(v_impl_1074_, 0);
lean_inc(v_size_1159_);
v___x_1160_ = lean_nat_add(v___x_1075_, v_size_1159_);
lean_dec(v_size_1159_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 3, v_impl_1074_);
lean_ctor_set(v___x_1071_, 0, v___x_1160_);
v___x_1162_ = v___x_1071_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v_impl_1074_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v_r_1069_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
if (lean_obj_tag(v_r_1069_) == 0)
{
lean_object* v_l_1164_; 
v_l_1164_ = lean_ctor_get(v_r_1069_, 3);
lean_inc(v_l_1164_);
if (lean_obj_tag(v_l_1164_) == 0)
{
lean_object* v_r_1165_; 
v_r_1165_ = lean_ctor_get(v_r_1069_, 4);
lean_inc(v_r_1165_);
if (lean_obj_tag(v_r_1165_) == 0)
{
lean_object* v_size_1166_; lean_object* v_k_1167_; lean_object* v_v_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1181_; 
v_size_1166_ = lean_ctor_get(v_r_1069_, 0);
v_k_1167_ = lean_ctor_get(v_r_1069_, 1);
v_v_1168_ = lean_ctor_get(v_r_1069_, 2);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_r_1069_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; lean_object* v_unused_1183_; 
v_unused_1182_ = lean_ctor_get(v_r_1069_, 4);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_r_1069_, 3);
lean_dec(v_unused_1183_);
v___x_1170_ = v_r_1069_;
v_isShared_1171_ = v_isSharedCheck_1181_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_v_1168_);
lean_inc(v_k_1167_);
lean_inc(v_size_1166_);
lean_dec(v_r_1069_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1181_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v_size_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v_size_1172_ = lean_ctor_get(v_l_1164_, 0);
v___x_1173_ = lean_nat_add(v___x_1075_, v_size_1166_);
lean_dec(v_size_1166_);
v___x_1174_ = lean_nat_add(v___x_1075_, v_size_1172_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 4, v_l_1164_);
lean_ctor_set(v___x_1170_, 3, v_impl_1074_);
lean_ctor_set(v___x_1170_, 2, v_v_1067_);
lean_ctor_set(v___x_1170_, 1, v_k_1066_);
lean_ctor_set(v___x_1170_, 0, v___x_1174_);
v___x_1176_ = v___x_1170_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_impl_1074_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v_l_1164_);
v___x_1176_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1178_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v_r_1165_);
lean_ctor_set(v___x_1071_, 3, v___x_1176_);
lean_ctor_set(v___x_1071_, 2, v_v_1168_);
lean_ctor_set(v___x_1071_, 1, v_k_1167_);
lean_ctor_set(v___x_1071_, 0, v___x_1173_);
v___x_1178_ = v___x_1071_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_k_1167_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_v_1168_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_r_1165_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v_k_1184_; lean_object* v_v_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1208_; 
v_k_1184_ = lean_ctor_get(v_r_1069_, 1);
v_v_1185_ = lean_ctor_get(v_r_1069_, 2);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_r_1069_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; lean_object* v_unused_1210_; lean_object* v_unused_1211_; 
v_unused_1209_ = lean_ctor_get(v_r_1069_, 4);
lean_dec(v_unused_1209_);
v_unused_1210_ = lean_ctor_get(v_r_1069_, 3);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_r_1069_, 0);
lean_dec(v_unused_1211_);
v___x_1187_ = v_r_1069_;
v_isShared_1188_ = v_isSharedCheck_1208_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_v_1185_);
lean_inc(v_k_1184_);
lean_dec(v_r_1069_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1208_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v_k_1189_; lean_object* v_v_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1204_; 
v_k_1189_ = lean_ctor_get(v_l_1164_, 1);
v_v_1190_ = lean_ctor_get(v_l_1164_, 2);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_l_1164_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; lean_object* v_unused_1206_; lean_object* v_unused_1207_; 
v_unused_1205_ = lean_ctor_get(v_l_1164_, 4);
lean_dec(v_unused_1205_);
v_unused_1206_ = lean_ctor_get(v_l_1164_, 3);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_l_1164_, 0);
lean_dec(v_unused_1207_);
v___x_1192_ = v_l_1164_;
v_isShared_1193_ = v_isSharedCheck_1204_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_v_1190_);
lean_inc(v_k_1189_);
lean_dec(v_l_1164_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1204_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_unsigned_to_nat(3u);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 4, v_r_1165_);
lean_ctor_set(v___x_1192_, 3, v_r_1165_);
lean_ctor_set(v___x_1192_, 2, v_v_1067_);
lean_ctor_set(v___x_1192_, 1, v_k_1066_);
lean_ctor_set(v___x_1192_, 0, v___x_1075_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_r_1165_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_r_1165_);
v___x_1196_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 3, v_r_1165_);
lean_ctor_set(v___x_1187_, 0, v___x_1075_);
v___x_1198_ = v___x_1187_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_k_1184_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_v_1185_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_r_1165_);
lean_ctor_set(v_reuseFailAlloc_1202_, 4, v_r_1165_);
v___x_1198_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v___x_1198_);
lean_ctor_set(v___x_1071_, 3, v___x_1196_);
lean_ctor_set(v___x_1071_, 2, v_v_1190_);
lean_ctor_set(v___x_1071_, 1, v_k_1189_);
lean_ctor_set(v___x_1071_, 0, v___x_1194_);
v___x_1200_ = v___x_1071_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_k_1189_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_v_1190_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1212_; 
v_r_1212_ = lean_ctor_get(v_r_1069_, 4);
lean_inc(v_r_1212_);
if (lean_obj_tag(v_r_1212_) == 0)
{
lean_object* v_k_1213_; lean_object* v_v_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1225_; 
v_k_1213_ = lean_ctor_get(v_r_1069_, 1);
v_v_1214_ = lean_ctor_get(v_r_1069_, 2);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_r_1069_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; lean_object* v_unused_1227_; lean_object* v_unused_1228_; 
v_unused_1226_ = lean_ctor_get(v_r_1069_, 4);
lean_dec(v_unused_1226_);
v_unused_1227_ = lean_ctor_get(v_r_1069_, 3);
lean_dec(v_unused_1227_);
v_unused_1228_ = lean_ctor_get(v_r_1069_, 0);
lean_dec(v_unused_1228_);
v___x_1216_ = v_r_1069_;
v_isShared_1217_ = v_isSharedCheck_1225_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_v_1214_);
lean_inc(v_k_1213_);
lean_dec(v_r_1069_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1225_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_unsigned_to_nat(3u);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 4, v_l_1164_);
lean_ctor_set(v___x_1216_, 2, v_v_1067_);
lean_ctor_set(v___x_1216_, 1, v_k_1066_);
lean_ctor_set(v___x_1216_, 0, v___x_1075_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_l_1164_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_l_1164_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v_r_1212_);
lean_ctor_set(v___x_1071_, 3, v___x_1220_);
lean_ctor_set(v___x_1071_, 2, v_v_1214_);
lean_ctor_set(v___x_1071_, 1, v_k_1213_);
lean_ctor_set(v___x_1071_, 0, v___x_1218_);
v___x_1222_ = v___x_1071_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_k_1213_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_v_1214_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_r_1212_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
else
{
lean_object* v_size_1229_; lean_object* v_k_1230_; lean_object* v_v_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1242_; 
v_size_1229_ = lean_ctor_get(v_r_1069_, 0);
v_k_1230_ = lean_ctor_get(v_r_1069_, 1);
v_v_1231_ = lean_ctor_get(v_r_1069_, 2);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_r_1069_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; lean_object* v_unused_1244_; 
v_unused_1243_ = lean_ctor_get(v_r_1069_, 4);
lean_dec(v_unused_1243_);
v_unused_1244_ = lean_ctor_get(v_r_1069_, 3);
lean_dec(v_unused_1244_);
v___x_1233_ = v_r_1069_;
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_v_1231_);
lean_inc(v_k_1230_);
lean_inc(v_size_1229_);
lean_dec(v_r_1069_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 3, v_r_1212_);
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_size_1229_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_k_1230_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_v_1231_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_r_1212_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_r_1212_);
v___x_1236_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1237_ = lean_unsigned_to_nat(2u);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v___x_1236_);
lean_ctor_set(v___x_1071_, 3, v_r_1212_);
lean_ctor_set(v___x_1071_, 0, v___x_1237_);
v___x_1239_ = v___x_1071_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_r_1212_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v___x_1236_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
}
else
{
lean_object* v___x_1246_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 3, v_r_1069_);
lean_ctor_set(v___x_1071_, 0, v___x_1075_);
v___x_1246_ = v___x_1071_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_r_1069_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_r_1069_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1071_);
lean_dec(v_v_1067_);
lean_dec(v_k_1066_);
if (lean_obj_tag(v_l_1068_) == 0)
{
if (lean_obj_tag(v_r_1069_) == 0)
{
lean_object* v_size_1248_; lean_object* v_k_1249_; lean_object* v_v_1250_; lean_object* v_l_1251_; lean_object* v_r_1252_; lean_object* v_size_1253_; lean_object* v_k_1254_; lean_object* v_v_1255_; lean_object* v_l_1256_; lean_object* v_r_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_size_1248_ = lean_ctor_get(v_l_1068_, 0);
v_k_1249_ = lean_ctor_get(v_l_1068_, 1);
v_v_1250_ = lean_ctor_get(v_l_1068_, 2);
v_l_1251_ = lean_ctor_get(v_l_1068_, 3);
v_r_1252_ = lean_ctor_get(v_l_1068_, 4);
lean_inc(v_r_1252_);
v_size_1253_ = lean_ctor_get(v_r_1069_, 0);
v_k_1254_ = lean_ctor_get(v_r_1069_, 1);
v_v_1255_ = lean_ctor_get(v_r_1069_, 2);
v_l_1256_ = lean_ctor_get(v_r_1069_, 3);
lean_inc(v_l_1256_);
v_r_1257_ = lean_ctor_get(v_r_1069_, 4);
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_nat_dec_lt(v_size_1248_, v_size_1253_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1395_; 
lean_inc(v_l_1251_);
lean_inc(v_v_1250_);
lean_inc(v_k_1249_);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_l_1068_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; lean_object* v_unused_1397_; lean_object* v_unused_1398_; lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1396_ = lean_ctor_get(v_l_1068_, 4);
lean_dec(v_unused_1396_);
v_unused_1397_ = lean_ctor_get(v_l_1068_, 3);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_l_1068_, 2);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_l_1068_, 1);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_l_1068_, 0);
lean_dec(v_unused_1400_);
v___x_1261_ = v_l_1068_;
v_isShared_1262_ = v_isSharedCheck_1395_;
goto v_resetjp_1260_;
}
else
{
lean_dec(v_l_1068_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1395_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v_tree_1264_; 
v___x_1263_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1249_, v_v_1250_, v_l_1251_, v_r_1252_);
v_tree_1264_ = lean_ctor_get(v___x_1263_, 2);
lean_inc(v_tree_1264_);
if (lean_obj_tag(v_tree_1264_) == 0)
{
lean_object* v_k_1265_; lean_object* v_v_1266_; lean_object* v_size_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_k_1265_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_k_1265_);
v_v_1266_ = lean_ctor_get(v___x_1263_, 1);
lean_inc(v_v_1266_);
lean_dec_ref(v___x_1263_);
v_size_1267_ = lean_ctor_get(v_tree_1264_, 0);
v___x_1268_ = lean_unsigned_to_nat(3u);
v___x_1269_ = lean_nat_mul(v___x_1268_, v_size_1267_);
v___x_1270_ = lean_nat_dec_lt(v___x_1269_, v_size_1253_);
lean_dec(v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
lean_dec(v_l_1256_);
v___x_1271_ = lean_nat_add(v___x_1258_, v_size_1267_);
v___x_1272_ = lean_nat_add(v___x_1271_, v_size_1253_);
lean_dec(v___x_1271_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_r_1069_);
lean_ctor_set(v___x_1261_, 3, v_tree_1264_);
lean_ctor_set(v___x_1261_, 2, v_v_1266_);
lean_ctor_set(v___x_1261_, 1, v_k_1265_);
lean_ctor_set(v___x_1261_, 0, v___x_1272_);
v___x_1274_ = v___x_1261_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_k_1265_);
lean_ctor_set(v_reuseFailAlloc_1275_, 2, v_v_1266_);
lean_ctor_set(v_reuseFailAlloc_1275_, 3, v_tree_1264_);
lean_ctor_set(v_reuseFailAlloc_1275_, 4, v_r_1069_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
else
{
lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1330_; 
lean_inc(v_r_1257_);
lean_inc(v_v_1255_);
lean_inc(v_k_1254_);
lean_inc(v_size_1253_);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_r_1069_);
if (v_isSharedCheck_1330_ == 0)
{
lean_object* v_unused_1331_; lean_object* v_unused_1332_; lean_object* v_unused_1333_; lean_object* v_unused_1334_; lean_object* v_unused_1335_; 
v_unused_1331_ = lean_ctor_get(v_r_1069_, 4);
lean_dec(v_unused_1331_);
v_unused_1332_ = lean_ctor_get(v_r_1069_, 3);
lean_dec(v_unused_1332_);
v_unused_1333_ = lean_ctor_get(v_r_1069_, 2);
lean_dec(v_unused_1333_);
v_unused_1334_ = lean_ctor_get(v_r_1069_, 1);
lean_dec(v_unused_1334_);
v_unused_1335_ = lean_ctor_get(v_r_1069_, 0);
lean_dec(v_unused_1335_);
v___x_1277_ = v_r_1069_;
v_isShared_1278_ = v_isSharedCheck_1330_;
goto v_resetjp_1276_;
}
else
{
lean_dec(v_r_1069_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1330_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_size_1279_; lean_object* v_k_1280_; lean_object* v_v_1281_; lean_object* v_l_1282_; lean_object* v_r_1283_; lean_object* v_size_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v_size_1279_ = lean_ctor_get(v_l_1256_, 0);
v_k_1280_ = lean_ctor_get(v_l_1256_, 1);
v_v_1281_ = lean_ctor_get(v_l_1256_, 2);
v_l_1282_ = lean_ctor_get(v_l_1256_, 3);
v_r_1283_ = lean_ctor_get(v_l_1256_, 4);
v_size_1284_ = lean_ctor_get(v_r_1257_, 0);
v___x_1285_ = lean_unsigned_to_nat(2u);
v___x_1286_ = lean_nat_mul(v___x_1285_, v_size_1284_);
v___x_1287_ = lean_nat_dec_lt(v_size_1279_, v___x_1286_);
lean_dec(v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1315_; 
lean_inc(v_r_1283_);
lean_inc(v_l_1282_);
lean_inc(v_v_1281_);
lean_inc(v_k_1280_);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_l_1256_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; lean_object* v_unused_1317_; lean_object* v_unused_1318_; lean_object* v_unused_1319_; lean_object* v_unused_1320_; 
v_unused_1316_ = lean_ctor_get(v_l_1256_, 4);
lean_dec(v_unused_1316_);
v_unused_1317_ = lean_ctor_get(v_l_1256_, 3);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_l_1256_, 2);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_l_1256_, 1);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_l_1256_, 0);
lean_dec(v_unused_1320_);
v___x_1289_ = v_l_1256_;
v_isShared_1290_ = v_isSharedCheck_1315_;
goto v_resetjp_1288_;
}
else
{
lean_dec(v_l_1256_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1315_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1305_; 
v___x_1291_ = lean_nat_add(v___x_1258_, v_size_1267_);
v___x_1292_ = lean_nat_add(v___x_1291_, v_size_1253_);
lean_dec(v_size_1253_);
if (lean_obj_tag(v_l_1282_) == 0)
{
lean_object* v_size_1313_; 
v_size_1313_ = lean_ctor_get(v_l_1282_, 0);
lean_inc(v_size_1313_);
v___y_1305_ = v_size_1313_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_unsigned_to_nat(0u);
v___y_1305_ = v___x_1314_;
goto v___jp_1304_;
}
v___jp_1293_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = lean_nat_add(v___y_1294_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec(v___y_1294_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 4, v_r_1257_);
lean_ctor_set(v___x_1289_, 3, v_r_1283_);
lean_ctor_set(v___x_1289_, 2, v_v_1255_);
lean_ctor_set(v___x_1289_, 1, v_k_1254_);
lean_ctor_set(v___x_1289_, 0, v___x_1297_);
v___x_1299_ = v___x_1289_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_r_1283_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_r_1257_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1301_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 4, v___x_1299_);
lean_ctor_set(v___x_1277_, 3, v___y_1295_);
lean_ctor_set(v___x_1277_, 2, v_v_1281_);
lean_ctor_set(v___x_1277_, 1, v_k_1280_);
lean_ctor_set(v___x_1277_, 0, v___x_1292_);
v___x_1301_ = v___x_1277_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v___y_1295_);
lean_ctor_set(v_reuseFailAlloc_1302_, 4, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
v___jp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = lean_nat_add(v___x_1291_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec(v___x_1291_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_l_1282_);
lean_ctor_set(v___x_1261_, 3, v_tree_1264_);
lean_ctor_set(v___x_1261_, 2, v_v_1266_);
lean_ctor_set(v___x_1261_, 1, v_k_1265_);
lean_ctor_set(v___x_1261_, 0, v___x_1306_);
v___x_1308_ = v___x_1261_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_k_1265_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_v_1266_);
lean_ctor_set(v_reuseFailAlloc_1312_, 3, v_tree_1264_);
lean_ctor_set(v_reuseFailAlloc_1312_, 4, v_l_1282_);
v___x_1308_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_nat_add(v___x_1258_, v_size_1284_);
if (lean_obj_tag(v_r_1283_) == 0)
{
lean_object* v_size_1310_; 
v_size_1310_ = lean_ctor_get(v_r_1283_, 0);
lean_inc(v_size_1310_);
v___y_1294_ = v___x_1309_;
v___y_1295_ = v___x_1308_;
v___y_1296_ = v_size_1310_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_unsigned_to_nat(0u);
v___y_1294_ = v___x_1309_;
v___y_1295_ = v___x_1308_;
v___y_1296_ = v___x_1311_;
goto v___jp_1293_;
}
}
}
}
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1321_ = lean_nat_add(v___x_1258_, v_size_1267_);
v___x_1322_ = lean_nat_add(v___x_1321_, v_size_1253_);
lean_dec(v_size_1253_);
v___x_1323_ = lean_nat_add(v___x_1321_, v_size_1279_);
lean_dec(v___x_1321_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 4, v_l_1256_);
lean_ctor_set(v___x_1277_, 3, v_tree_1264_);
lean_ctor_set(v___x_1277_, 2, v_v_1266_);
lean_ctor_set(v___x_1277_, 1, v_k_1265_);
lean_ctor_set(v___x_1277_, 0, v___x_1323_);
v___x_1325_ = v___x_1277_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_k_1265_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_v_1266_);
lean_ctor_set(v_reuseFailAlloc_1329_, 3, v_tree_1264_);
lean_ctor_set(v_reuseFailAlloc_1329_, 4, v_l_1256_);
v___x_1325_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1327_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_r_1257_);
lean_ctor_set(v___x_1261_, 3, v___x_1325_);
lean_ctor_set(v___x_1261_, 2, v_v_1255_);
lean_ctor_set(v___x_1261_, 1, v_k_1254_);
lean_ctor_set(v___x_1261_, 0, v___x_1322_);
v___x_1327_ = v___x_1261_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_r_1257_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
}
else
{
lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1389_; 
lean_inc(v_r_1257_);
lean_inc(v_v_1255_);
lean_inc(v_k_1254_);
lean_inc(v_size_1253_);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_r_1069_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; lean_object* v_unused_1391_; lean_object* v_unused_1392_; lean_object* v_unused_1393_; lean_object* v_unused_1394_; 
v_unused_1390_ = lean_ctor_get(v_r_1069_, 4);
lean_dec(v_unused_1390_);
v_unused_1391_ = lean_ctor_get(v_r_1069_, 3);
lean_dec(v_unused_1391_);
v_unused_1392_ = lean_ctor_get(v_r_1069_, 2);
lean_dec(v_unused_1392_);
v_unused_1393_ = lean_ctor_get(v_r_1069_, 1);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v_r_1069_, 0);
lean_dec(v_unused_1394_);
v___x_1337_ = v_r_1069_;
v_isShared_1338_ = v_isSharedCheck_1389_;
goto v_resetjp_1336_;
}
else
{
lean_dec(v_r_1069_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1389_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
if (lean_obj_tag(v_l_1256_) == 0)
{
if (lean_obj_tag(v_r_1257_) == 0)
{
lean_object* v_k_1339_; lean_object* v_v_1340_; lean_object* v_size_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v_k_1339_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_k_1339_);
v_v_1340_ = lean_ctor_get(v___x_1263_, 1);
lean_inc(v_v_1340_);
lean_dec_ref(v___x_1263_);
v_size_1341_ = lean_ctor_get(v_l_1256_, 0);
v___x_1342_ = lean_nat_add(v___x_1258_, v_size_1253_);
lean_dec(v_size_1253_);
v___x_1343_ = lean_nat_add(v___x_1258_, v_size_1341_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 4, v_l_1256_);
lean_ctor_set(v___x_1337_, 3, v_tree_1264_);
lean_ctor_set(v___x_1337_, 2, v_v_1340_);
lean_ctor_set(v___x_1337_, 1, v_k_1339_);
lean_ctor_set(v___x_1337_, 0, v___x_1343_);
v___x_1345_ = v___x_1337_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_1339_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_1340_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_tree_1264_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_l_1256_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_r_1257_);
lean_ctor_set(v___x_1261_, 3, v___x_1345_);
lean_ctor_set(v___x_1261_, 2, v_v_1255_);
lean_ctor_set(v___x_1261_, 1, v_k_1254_);
lean_ctor_set(v___x_1261_, 0, v___x_1342_);
v___x_1347_ = v___x_1261_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1348_, 3, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1348_, 4, v_r_1257_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
else
{
lean_object* v_k_1350_; lean_object* v_v_1351_; lean_object* v_k_1352_; lean_object* v_v_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_size_1253_);
v_k_1350_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_k_1350_);
v_v_1351_ = lean_ctor_get(v___x_1263_, 1);
lean_inc(v_v_1351_);
lean_dec_ref(v___x_1263_);
v_k_1352_ = lean_ctor_get(v_l_1256_, 1);
v_v_1353_ = lean_ctor_get(v_l_1256_, 2);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_l_1256_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; lean_object* v_unused_1369_; lean_object* v_unused_1370_; 
v_unused_1368_ = lean_ctor_get(v_l_1256_, 4);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_l_1256_, 3);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_l_1256_, 0);
lean_dec(v_unused_1370_);
v___x_1355_ = v_l_1256_;
v_isShared_1356_ = v_isSharedCheck_1367_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_v_1353_);
lean_inc(v_k_1352_);
lean_dec(v_l_1256_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1367_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_unsigned_to_nat(3u);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 4, v_r_1257_);
lean_ctor_set(v___x_1355_, 3, v_r_1257_);
lean_ctor_set(v___x_1355_, 2, v_v_1351_);
lean_ctor_set(v___x_1355_, 1, v_k_1350_);
lean_ctor_set(v___x_1355_, 0, v___x_1258_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1350_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1351_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_r_1257_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_r_1257_);
v___x_1359_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1361_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 3, v_r_1257_);
lean_ctor_set(v___x_1337_, 0, v___x_1258_);
v___x_1361_ = v___x_1337_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_r_1257_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_r_1257_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1361_);
lean_ctor_set(v___x_1261_, 3, v___x_1359_);
lean_ctor_set(v___x_1261_, 2, v_v_1353_);
lean_ctor_set(v___x_1261_, 1, v_k_1352_);
lean_ctor_set(v___x_1261_, 0, v___x_1357_);
v___x_1363_ = v___x_1261_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1257_) == 0)
{
lean_object* v_k_1371_; lean_object* v_v_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_dec(v_size_1253_);
v_k_1371_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_k_1371_);
v_v_1372_ = lean_ctor_get(v___x_1263_, 1);
lean_inc(v_v_1372_);
lean_dec_ref(v___x_1263_);
v___x_1373_ = lean_unsigned_to_nat(3u);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 4, v_l_1256_);
lean_ctor_set(v___x_1337_, 2, v_v_1372_);
lean_ctor_set(v___x_1337_, 1, v_k_1371_);
lean_ctor_set(v___x_1337_, 0, v___x_1258_);
v___x_1375_ = v___x_1337_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_l_1256_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v_l_1256_);
v___x_1375_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1377_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_r_1257_);
lean_ctor_set(v___x_1261_, 3, v___x_1375_);
lean_ctor_set(v___x_1261_, 2, v_v_1255_);
lean_ctor_set(v___x_1261_, 1, v_k_1254_);
lean_ctor_set(v___x_1261_, 0, v___x_1373_);
v___x_1377_ = v___x_1261_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1378_, 3, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1378_, 4, v_r_1257_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_object* v_k_1380_; lean_object* v_v_1381_; lean_object* v___x_1383_; 
v_k_1380_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_k_1380_);
v_v_1381_ = lean_ctor_get(v___x_1263_, 1);
lean_inc(v_v_1381_);
lean_dec_ref(v___x_1263_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 3, v_r_1257_);
v___x_1383_ = v___x_1337_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_size_1253_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1388_, 3, v_r_1257_);
lean_ctor_set(v_reuseFailAlloc_1388_, 4, v_r_1257_);
v___x_1383_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1384_ = lean_unsigned_to_nat(2u);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___x_1383_);
lean_ctor_set(v___x_1261_, 3, v_r_1257_);
lean_ctor_set(v___x_1261_, 2, v_v_1381_);
lean_ctor_set(v___x_1261_, 1, v_k_1380_);
lean_ctor_set(v___x_1261_, 0, v___x_1384_);
v___x_1386_ = v___x_1261_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_k_1380_);
lean_ctor_set(v_reuseFailAlloc_1387_, 2, v_v_1381_);
lean_ctor_set(v_reuseFailAlloc_1387_, 3, v_r_1257_);
lean_ctor_set(v_reuseFailAlloc_1387_, 4, v___x_1383_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
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
lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1553_; 
lean_inc(v_r_1257_);
lean_inc(v_v_1255_);
lean_inc(v_k_1254_);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_r_1069_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; lean_object* v_unused_1555_; lean_object* v_unused_1556_; lean_object* v_unused_1557_; lean_object* v_unused_1558_; 
v_unused_1554_ = lean_ctor_get(v_r_1069_, 4);
lean_dec(v_unused_1554_);
v_unused_1555_ = lean_ctor_get(v_r_1069_, 3);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_r_1069_, 2);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v_r_1069_, 1);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v_r_1069_, 0);
lean_dec(v_unused_1558_);
v___x_1402_ = v_r_1069_;
v_isShared_1403_ = v_isSharedCheck_1553_;
goto v_resetjp_1401_;
}
else
{
lean_dec(v_r_1069_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1553_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v_tree_1405_; 
v___x_1404_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1254_, v_v_1255_, v_l_1256_, v_r_1257_);
v_tree_1405_ = lean_ctor_get(v___x_1404_, 2);
lean_inc(v_tree_1405_);
if (lean_obj_tag(v_tree_1405_) == 0)
{
lean_object* v_k_1406_; lean_object* v_v_1407_; lean_object* v_size_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v_k_1406_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_k_1406_);
v_v_1407_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_v_1407_);
lean_dec_ref(v___x_1404_);
v_size_1408_ = lean_ctor_get(v_tree_1405_, 0);
v___x_1409_ = lean_unsigned_to_nat(3u);
v___x_1410_ = lean_nat_mul(v___x_1409_, v_size_1408_);
v___x_1411_ = lean_nat_dec_lt(v___x_1410_, v_size_1248_);
lean_dec(v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
lean_dec(v_r_1252_);
v___x_1412_ = lean_nat_add(v___x_1258_, v_size_1248_);
v___x_1413_ = lean_nat_add(v___x_1412_, v_size_1408_);
lean_dec(v___x_1412_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 4, v_tree_1405_);
lean_ctor_set(v___x_1402_, 3, v_l_1068_);
lean_ctor_set(v___x_1402_, 2, v_v_1407_);
lean_ctor_set(v___x_1402_, 1, v_k_1406_);
lean_ctor_set(v___x_1402_, 0, v___x_1413_);
v___x_1415_ = v___x_1402_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1406_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1407_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_l_1068_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_tree_1405_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
else
{
lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1482_; 
lean_inc(v_l_1251_);
lean_inc(v_v_1250_);
lean_inc(v_k_1249_);
lean_inc(v_size_1248_);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_l_1068_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; lean_object* v_unused_1487_; 
v_unused_1483_ = lean_ctor_get(v_l_1068_, 4);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_l_1068_, 3);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_l_1068_, 2);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_l_1068_, 1);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_l_1068_, 0);
lean_dec(v_unused_1487_);
v___x_1418_ = v_l_1068_;
v_isShared_1419_ = v_isSharedCheck_1482_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v_l_1068_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1482_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_size_1420_; lean_object* v_size_1421_; lean_object* v_k_1422_; lean_object* v_v_1423_; lean_object* v_l_1424_; lean_object* v_r_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v_size_1420_ = lean_ctor_get(v_l_1251_, 0);
v_size_1421_ = lean_ctor_get(v_r_1252_, 0);
v_k_1422_ = lean_ctor_get(v_r_1252_, 1);
v_v_1423_ = lean_ctor_get(v_r_1252_, 2);
v_l_1424_ = lean_ctor_get(v_r_1252_, 3);
v_r_1425_ = lean_ctor_get(v_r_1252_, 4);
v___x_1426_ = lean_unsigned_to_nat(2u);
v___x_1427_ = lean_nat_mul(v___x_1426_, v_size_1420_);
v___x_1428_ = lean_nat_dec_lt(v_size_1421_, v___x_1427_);
lean_dec(v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1466_; 
lean_inc(v_r_1425_);
lean_inc(v_l_1424_);
lean_inc(v_v_1423_);
lean_inc(v_k_1422_);
lean_del_object(v___x_1418_);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_r_1252_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; 
v_unused_1467_ = lean_ctor_get(v_r_1252_, 4);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_r_1252_, 3);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_r_1252_, 2);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_r_1252_, 1);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_r_1252_, 0);
lean_dec(v_unused_1471_);
v___x_1430_ = v_r_1252_;
v_isShared_1431_ = v_isSharedCheck_1466_;
goto v_resetjp_1429_;
}
else
{
lean_dec(v_r_1252_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1466_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___x_1454_; lean_object* v___y_1456_; 
v___x_1432_ = lean_nat_add(v___x_1258_, v_size_1248_);
lean_dec(v_size_1248_);
v___x_1433_ = lean_nat_add(v___x_1432_, v_size_1408_);
lean_dec(v___x_1432_);
v___x_1454_ = lean_nat_add(v___x_1258_, v_size_1420_);
if (lean_obj_tag(v_l_1424_) == 0)
{
lean_object* v_size_1464_; 
v_size_1464_ = lean_ctor_get(v_l_1424_, 0);
lean_inc(v_size_1464_);
v___y_1456_ = v_size_1464_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_unsigned_to_nat(0u);
v___y_1456_ = v___x_1465_;
goto v___jp_1455_;
}
v___jp_1434_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_nat_add(v___y_1435_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec(v___y_1435_);
lean_inc_ref(v_tree_1405_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v_tree_1405_);
lean_ctor_set(v___x_1430_, 3, v_r_1425_);
lean_ctor_set(v___x_1430_, 2, v_v_1407_);
lean_ctor_set(v___x_1430_, 1, v_k_1406_);
lean_ctor_set(v___x_1430_, 0, v___x_1438_);
v___x_1440_ = v___x_1430_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_k_1406_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_v_1407_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_r_1425_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_tree_1405_);
v___x_1440_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
v_isSharedCheck_1447_ = !lean_is_exclusive(v_tree_1405_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1448_ = lean_ctor_get(v_tree_1405_, 4);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_tree_1405_, 3);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_tree_1405_, 2);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_tree_1405_, 1);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_tree_1405_, 0);
lean_dec(v_unused_1452_);
v___x_1442_ = v_tree_1405_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_dec(v_tree_1405_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 4, v___x_1440_);
lean_ctor_set(v___x_1442_, 3, v___y_1436_);
lean_ctor_set(v___x_1442_, 2, v_v_1423_);
lean_ctor_set(v___x_1442_, 1, v_k_1422_);
lean_ctor_set(v___x_1442_, 0, v___x_1433_);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_k_1422_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_v_1423_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v___y_1436_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v___x_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
v___jp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1457_ = lean_nat_add(v___x_1454_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec(v___x_1454_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 4, v_l_1424_);
lean_ctor_set(v___x_1402_, 3, v_l_1251_);
lean_ctor_set(v___x_1402_, 2, v_v_1250_);
lean_ctor_set(v___x_1402_, 1, v_k_1249_);
lean_ctor_set(v___x_1402_, 0, v___x_1457_);
v___x_1459_ = v___x_1402_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v_l_1424_);
v___x_1459_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_nat_add(v___x_1258_, v_size_1408_);
if (lean_obj_tag(v_r_1425_) == 0)
{
lean_object* v_size_1461_; 
v_size_1461_ = lean_ctor_get(v_r_1425_, 0);
lean_inc(v_size_1461_);
v___y_1435_ = v___x_1460_;
v___y_1436_ = v___x_1459_;
v___y_1437_ = v_size_1461_;
goto v___jp_1434_;
}
else
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_unsigned_to_nat(0u);
v___y_1435_ = v___x_1460_;
v___y_1436_ = v___x_1459_;
v___y_1437_ = v___x_1462_;
goto v___jp_1434_;
}
}
}
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1472_ = lean_nat_add(v___x_1258_, v_size_1248_);
lean_dec(v_size_1248_);
v___x_1473_ = lean_nat_add(v___x_1472_, v_size_1408_);
lean_dec(v___x_1472_);
v___x_1474_ = lean_nat_add(v___x_1258_, v_size_1408_);
v___x_1475_ = lean_nat_add(v___x_1474_, v_size_1421_);
lean_dec(v___x_1474_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 4, v_tree_1405_);
lean_ctor_set(v___x_1402_, 3, v_r_1252_);
lean_ctor_set(v___x_1402_, 2, v_v_1407_);
lean_ctor_set(v___x_1402_, 1, v_k_1406_);
lean_ctor_set(v___x_1402_, 0, v___x_1475_);
v___x_1477_ = v___x_1402_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1406_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1407_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_r_1252_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_tree_1405_);
v___x_1477_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 4, v___x_1477_);
lean_ctor_set(v___x_1418_, 0, v___x_1473_);
v___x_1479_ = v___x_1418_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1251_) == 0)
{
lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1511_; 
lean_inc_ref(v_l_1251_);
lean_inc(v_v_1250_);
lean_inc(v_k_1249_);
lean_inc(v_size_1248_);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_l_1068_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; lean_object* v_unused_1515_; lean_object* v_unused_1516_; 
v_unused_1512_ = lean_ctor_get(v_l_1068_, 4);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_l_1068_, 3);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_l_1068_, 2);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v_l_1068_, 1);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_l_1068_, 0);
lean_dec(v_unused_1516_);
v___x_1489_ = v_l_1068_;
v_isShared_1490_ = v_isSharedCheck_1511_;
goto v_resetjp_1488_;
}
else
{
lean_dec(v_l_1068_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1511_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
if (lean_obj_tag(v_r_1252_) == 0)
{
lean_object* v_k_1491_; lean_object* v_v_1492_; lean_object* v_size_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v_k_1491_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_k_1491_);
v_v_1492_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_v_1492_);
lean_dec_ref(v___x_1404_);
v_size_1493_ = lean_ctor_get(v_r_1252_, 0);
v___x_1494_ = lean_nat_add(v___x_1258_, v_size_1248_);
lean_dec(v_size_1248_);
v___x_1495_ = lean_nat_add(v___x_1258_, v_size_1493_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 4, v_tree_1405_);
lean_ctor_set(v___x_1402_, 3, v_r_1252_);
lean_ctor_set(v___x_1402_, 2, v_v_1492_);
lean_ctor_set(v___x_1402_, 1, v_k_1491_);
lean_ctor_set(v___x_1402_, 0, v___x_1495_);
v___x_1497_ = v___x_1402_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1491_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1492_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_r_1252_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_tree_1405_);
v___x_1497_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 4, v___x_1497_);
lean_ctor_set(v___x_1489_, 0, v___x_1494_);
v___x_1499_ = v___x_1489_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
else
{
lean_object* v_k_1502_; lean_object* v_v_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
lean_dec(v_size_1248_);
v_k_1502_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_k_1502_);
v_v_1503_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_v_1503_);
lean_dec_ref(v___x_1404_);
v___x_1504_ = lean_unsigned_to_nat(3u);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 4, v_r_1252_);
lean_ctor_set(v___x_1402_, 3, v_r_1252_);
lean_ctor_set(v___x_1402_, 2, v_v_1503_);
lean_ctor_set(v___x_1402_, 1, v_k_1502_);
lean_ctor_set(v___x_1402_, 0, v___x_1258_);
v___x_1506_ = v___x_1402_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_k_1502_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_v_1503_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v_r_1252_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_r_1252_);
v___x_1506_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1508_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 4, v___x_1506_);
lean_ctor_set(v___x_1489_, 0, v___x_1504_);
v___x_1508_ = v___x_1489_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1252_) == 0)
{
lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1541_; 
lean_inc(v_l_1251_);
lean_inc(v_v_1250_);
lean_inc(v_k_1249_);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_l_1068_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; lean_object* v_unused_1543_; lean_object* v_unused_1544_; lean_object* v_unused_1545_; lean_object* v_unused_1546_; 
v_unused_1542_ = lean_ctor_get(v_l_1068_, 4);
lean_dec(v_unused_1542_);
v_unused_1543_ = lean_ctor_get(v_l_1068_, 3);
lean_dec(v_unused_1543_);
v_unused_1544_ = lean_ctor_get(v_l_1068_, 2);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v_l_1068_, 1);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_l_1068_, 0);
lean_dec(v_unused_1546_);
v___x_1518_ = v_l_1068_;
v_isShared_1519_ = v_isSharedCheck_1541_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v_l_1068_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1541_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_k_1520_; lean_object* v_v_1521_; lean_object* v_k_1522_; lean_object* v_v_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1537_; 
v_k_1520_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_k_1520_);
v_v_1521_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_v_1521_);
lean_dec_ref(v___x_1404_);
v_k_1522_ = lean_ctor_get(v_r_1252_, 1);
v_v_1523_ = lean_ctor_get(v_r_1252_, 2);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_r_1252_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; 
v_unused_1538_ = lean_ctor_get(v_r_1252_, 4);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_r_1252_, 3);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_r_1252_, 0);
lean_dec(v_unused_1540_);
v___x_1525_ = v_r_1252_;
v_isShared_1526_ = v_isSharedCheck_1537_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_v_1523_);
lean_inc(v_k_1522_);
lean_dec(v_r_1252_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1537_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1527_ = lean_unsigned_to_nat(3u);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 4, v_l_1251_);
lean_ctor_set(v___x_1525_, 3, v_l_1251_);
lean_ctor_set(v___x_1525_, 2, v_v_1250_);
lean_ctor_set(v___x_1525_, 1, v_k_1249_);
lean_ctor_set(v___x_1525_, 0, v___x_1258_);
v___x_1529_ = v___x_1525_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_l_1251_);
v___x_1529_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1531_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 4, v_l_1251_);
lean_ctor_set(v___x_1402_, 3, v_l_1251_);
lean_ctor_set(v___x_1402_, 2, v_v_1521_);
lean_ctor_set(v___x_1402_, 1, v_k_1520_);
lean_ctor_set(v___x_1402_, 0, v___x_1258_);
v___x_1531_ = v___x_1402_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_k_1520_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_v_1521_);
lean_ctor_set(v_reuseFailAlloc_1535_, 3, v_l_1251_);
lean_ctor_set(v_reuseFailAlloc_1535_, 4, v_l_1251_);
v___x_1531_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 4, v___x_1531_);
lean_ctor_set(v___x_1518_, 3, v___x_1529_);
lean_ctor_set(v___x_1518_, 2, v_v_1523_);
lean_ctor_set(v___x_1518_, 1, v_k_1522_);
lean_ctor_set(v___x_1518_, 0, v___x_1527_);
v___x_1533_ = v___x_1518_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_k_1522_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_v_1523_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
}
else
{
lean_object* v_k_1547_; lean_object* v_v_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
v_k_1547_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_k_1547_);
v_v_1548_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_v_1548_);
lean_dec_ref(v___x_1404_);
v___x_1549_ = lean_unsigned_to_nat(2u);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 4, v_r_1252_);
lean_ctor_set(v___x_1402_, 3, v_l_1068_);
lean_ctor_set(v___x_1402_, 2, v_v_1548_);
lean_ctor_set(v___x_1402_, 1, v_k_1547_);
lean_ctor_set(v___x_1402_, 0, v___x_1549_);
v___x_1551_ = v___x_1402_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_k_1547_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_v_1548_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_l_1068_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v_r_1252_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
}
}
else
{
return v_l_1068_;
}
}
else
{
return v_r_1069_;
}
}
default: 
{
lean_object* v_impl_1559_; lean_object* v___x_1560_; 
v_impl_1559_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1064_, v_r_1069_);
v___x_1560_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1559_) == 0)
{
if (lean_obj_tag(v_l_1068_) == 0)
{
lean_object* v_size_1561_; lean_object* v_size_1562_; lean_object* v_k_1563_; lean_object* v_v_1564_; lean_object* v_l_1565_; lean_object* v_r_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v_size_1561_ = lean_ctor_get(v_impl_1559_, 0);
lean_inc(v_size_1561_);
v_size_1562_ = lean_ctor_get(v_l_1068_, 0);
v_k_1563_ = lean_ctor_get(v_l_1068_, 1);
v_v_1564_ = lean_ctor_get(v_l_1068_, 2);
v_l_1565_ = lean_ctor_get(v_l_1068_, 3);
v_r_1566_ = lean_ctor_get(v_l_1068_, 4);
lean_inc(v_r_1566_);
v___x_1567_ = lean_unsigned_to_nat(3u);
v___x_1568_ = lean_nat_mul(v___x_1567_, v_size_1561_);
v___x_1569_ = lean_nat_dec_lt(v___x_1568_, v_size_1562_);
lean_dec(v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
lean_dec(v_r_1566_);
v___x_1570_ = lean_nat_add(v___x_1560_, v_size_1562_);
v___x_1571_ = lean_nat_add(v___x_1570_, v_size_1561_);
lean_dec(v_size_1561_);
lean_dec(v___x_1570_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v_impl_1559_);
lean_ctor_set(v___x_1071_, 0, v___x_1571_);
v___x_1573_ = v___x_1071_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v_l_1068_);
lean_ctor_set(v_reuseFailAlloc_1574_, 4, v_impl_1559_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1640_; 
lean_inc(v_l_1565_);
lean_inc(v_v_1564_);
lean_inc(v_k_1563_);
lean_inc(v_size_1562_);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_l_1068_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; lean_object* v_unused_1643_; lean_object* v_unused_1644_; lean_object* v_unused_1645_; 
v_unused_1641_ = lean_ctor_get(v_l_1068_, 4);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_l_1068_, 3);
lean_dec(v_unused_1642_);
v_unused_1643_ = lean_ctor_get(v_l_1068_, 2);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_l_1068_, 1);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_l_1068_, 0);
lean_dec(v_unused_1645_);
v___x_1576_ = v_l_1068_;
v_isShared_1577_ = v_isSharedCheck_1640_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v_l_1068_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1640_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_size_1578_; lean_object* v_size_1579_; lean_object* v_k_1580_; lean_object* v_v_1581_; lean_object* v_l_1582_; lean_object* v_r_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v_size_1578_ = lean_ctor_get(v_l_1565_, 0);
v_size_1579_ = lean_ctor_get(v_r_1566_, 0);
v_k_1580_ = lean_ctor_get(v_r_1566_, 1);
v_v_1581_ = lean_ctor_get(v_r_1566_, 2);
v_l_1582_ = lean_ctor_get(v_r_1566_, 3);
v_r_1583_ = lean_ctor_get(v_r_1566_, 4);
v___x_1584_ = lean_unsigned_to_nat(2u);
v___x_1585_ = lean_nat_mul(v___x_1584_, v_size_1578_);
v___x_1586_ = lean_nat_dec_lt(v_size_1579_, v___x_1585_);
lean_dec(v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1615_; 
lean_inc(v_r_1583_);
lean_inc(v_l_1582_);
lean_inc(v_v_1581_);
lean_inc(v_k_1580_);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_r_1566_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; lean_object* v_unused_1617_; lean_object* v_unused_1618_; lean_object* v_unused_1619_; lean_object* v_unused_1620_; 
v_unused_1616_ = lean_ctor_get(v_r_1566_, 4);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_r_1566_, 3);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_r_1566_, 2);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_r_1566_, 1);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v_r_1566_, 0);
lean_dec(v_unused_1620_);
v___x_1588_ = v_r_1566_;
v_isShared_1589_ = v_isSharedCheck_1615_;
goto v_resetjp_1587_;
}
else
{
lean_dec(v_r_1566_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1615_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___x_1603_; lean_object* v___y_1605_; 
v___x_1590_ = lean_nat_add(v___x_1560_, v_size_1562_);
lean_dec(v_size_1562_);
v___x_1591_ = lean_nat_add(v___x_1590_, v_size_1561_);
lean_dec(v___x_1590_);
v___x_1603_ = lean_nat_add(v___x_1560_, v_size_1578_);
if (lean_obj_tag(v_l_1582_) == 0)
{
lean_object* v_size_1613_; 
v_size_1613_ = lean_ctor_get(v_l_1582_, 0);
lean_inc(v_size_1613_);
v___y_1605_ = v_size_1613_;
goto v___jp_1604_;
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_unsigned_to_nat(0u);
v___y_1605_ = v___x_1614_;
goto v___jp_1604_;
}
v___jp_1592_:
{
lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1596_ = lean_nat_add(v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec(v___y_1594_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 4, v_impl_1559_);
lean_ctor_set(v___x_1588_, 3, v_r_1583_);
lean_ctor_set(v___x_1588_, 2, v_v_1067_);
lean_ctor_set(v___x_1588_, 1, v_k_1066_);
lean_ctor_set(v___x_1588_, 0, v___x_1596_);
v___x_1598_ = v___x_1588_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_r_1583_);
lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_impl_1559_);
v___x_1598_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 4, v___x_1598_);
lean_ctor_set(v___x_1576_, 3, v___y_1593_);
lean_ctor_set(v___x_1576_, 2, v_v_1581_);
lean_ctor_set(v___x_1576_, 1, v_k_1580_);
lean_ctor_set(v___x_1576_, 0, v___x_1591_);
v___x_1600_ = v___x_1576_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1580_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1581_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v___y_1593_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
v___jp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = lean_nat_add(v___x_1603_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec(v___x_1603_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v_l_1582_);
lean_ctor_set(v___x_1071_, 3, v_l_1565_);
lean_ctor_set(v___x_1071_, 2, v_v_1564_);
lean_ctor_set(v___x_1071_, 1, v_k_1563_);
lean_ctor_set(v___x_1071_, 0, v___x_1606_);
v___x_1608_ = v___x_1071_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_k_1563_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_v_1564_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v_l_1565_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v_l_1582_);
v___x_1608_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_nat_add(v___x_1560_, v_size_1561_);
lean_dec(v_size_1561_);
if (lean_obj_tag(v_r_1583_) == 0)
{
lean_object* v_size_1610_; 
v_size_1610_ = lean_ctor_get(v_r_1583_, 0);
lean_inc(v_size_1610_);
v___y_1593_ = v___x_1608_;
v___y_1594_ = v___x_1609_;
v___y_1595_ = v_size_1610_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_unsigned_to_nat(0u);
v___y_1593_ = v___x_1608_;
v___y_1594_ = v___x_1609_;
v___y_1595_ = v___x_1611_;
goto v___jp_1592_;
}
}
}
}
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
lean_del_object(v___x_1071_);
v___x_1621_ = lean_nat_add(v___x_1560_, v_size_1562_);
lean_dec(v_size_1562_);
v___x_1622_ = lean_nat_add(v___x_1621_, v_size_1561_);
lean_dec(v___x_1621_);
v___x_1623_ = lean_nat_add(v___x_1560_, v_size_1561_);
lean_dec(v_size_1561_);
v___x_1624_ = lean_nat_add(v___x_1623_, v_size_1579_);
lean_dec(v___x_1623_);
lean_inc_ref(v_impl_1559_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 4, v_impl_1559_);
lean_ctor_set(v___x_1576_, 3, v_r_1566_);
lean_ctor_set(v___x_1576_, 2, v_v_1067_);
lean_ctor_set(v___x_1576_, 1, v_k_1066_);
lean_ctor_set(v___x_1576_, 0, v___x_1624_);
v___x_1626_ = v___x_1576_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_r_1566_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v_impl_1559_);
v___x_1626_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_isSharedCheck_1633_ = !lean_is_exclusive(v_impl_1559_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; lean_object* v_unused_1635_; lean_object* v_unused_1636_; lean_object* v_unused_1637_; lean_object* v_unused_1638_; 
v_unused_1634_ = lean_ctor_get(v_impl_1559_, 4);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_impl_1559_, 3);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_impl_1559_, 2);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_impl_1559_, 1);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_impl_1559_, 0);
lean_dec(v_unused_1638_);
v___x_1628_ = v_impl_1559_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_dec(v_impl_1559_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 4, v___x_1626_);
lean_ctor_set(v___x_1628_, 3, v_l_1565_);
lean_ctor_set(v___x_1628_, 2, v_v_1564_);
lean_ctor_set(v___x_1628_, 1, v_k_1563_);
lean_ctor_set(v___x_1628_, 0, v___x_1622_);
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_k_1563_);
lean_ctor_set(v_reuseFailAlloc_1632_, 2, v_v_1564_);
lean_ctor_set(v_reuseFailAlloc_1632_, 3, v_l_1565_);
lean_ctor_set(v_reuseFailAlloc_1632_, 4, v___x_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v_size_1646_ = lean_ctor_get(v_impl_1559_, 0);
lean_inc(v_size_1646_);
v___x_1647_ = lean_nat_add(v___x_1560_, v_size_1646_);
lean_dec(v_size_1646_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v_impl_1559_);
lean_ctor_set(v___x_1071_, 0, v___x_1647_);
v___x_1649_ = v___x_1071_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_l_1068_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_impl_1559_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
if (lean_obj_tag(v_l_1068_) == 0)
{
lean_object* v_l_1651_; 
v_l_1651_ = lean_ctor_get(v_l_1068_, 3);
if (lean_obj_tag(v_l_1651_) == 0)
{
lean_object* v_r_1652_; 
lean_inc_ref(v_l_1651_);
v_r_1652_ = lean_ctor_get(v_l_1068_, 4);
lean_inc(v_r_1652_);
if (lean_obj_tag(v_r_1652_) == 0)
{
lean_object* v_size_1653_; lean_object* v_k_1654_; lean_object* v_v_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1668_; 
v_size_1653_ = lean_ctor_get(v_l_1068_, 0);
v_k_1654_ = lean_ctor_get(v_l_1068_, 1);
v_v_1655_ = lean_ctor_get(v_l_1068_, 2);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_l_1068_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; lean_object* v_unused_1670_; 
v_unused_1669_ = lean_ctor_get(v_l_1068_, 4);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_l_1068_, 3);
lean_dec(v_unused_1670_);
v___x_1657_ = v_l_1068_;
v_isShared_1658_ = v_isSharedCheck_1668_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_v_1655_);
lean_inc(v_k_1654_);
lean_inc(v_size_1653_);
lean_dec(v_l_1068_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1668_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v_size_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
v_size_1659_ = lean_ctor_get(v_r_1652_, 0);
v___x_1660_ = lean_nat_add(v___x_1560_, v_size_1653_);
lean_dec(v_size_1653_);
v___x_1661_ = lean_nat_add(v___x_1560_, v_size_1659_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 4, v_impl_1559_);
lean_ctor_set(v___x_1657_, 3, v_r_1652_);
lean_ctor_set(v___x_1657_, 2, v_v_1067_);
lean_ctor_set(v___x_1657_, 1, v_k_1066_);
lean_ctor_set(v___x_1657_, 0, v___x_1661_);
v___x_1663_ = v___x_1657_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_r_1652_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_impl_1559_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v___x_1663_);
lean_ctor_set(v___x_1071_, 3, v_l_1651_);
lean_ctor_set(v___x_1071_, 2, v_v_1655_);
lean_ctor_set(v___x_1071_, 1, v_k_1654_);
lean_ctor_set(v___x_1071_, 0, v___x_1660_);
v___x_1665_ = v___x_1071_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_k_1654_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_v_1655_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v_l_1651_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v_k_1671_; lean_object* v_v_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1683_; 
v_k_1671_ = lean_ctor_get(v_l_1068_, 1);
v_v_1672_ = lean_ctor_get(v_l_1068_, 2);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_l_1068_);
if (v_isSharedCheck_1683_ == 0)
{
lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; 
v_unused_1684_ = lean_ctor_get(v_l_1068_, 4);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_l_1068_, 3);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_l_1068_, 0);
lean_dec(v_unused_1686_);
v___x_1674_ = v_l_1068_;
v_isShared_1675_ = v_isSharedCheck_1683_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_v_1672_);
lean_inc(v_k_1671_);
lean_dec(v_l_1068_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1683_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = lean_unsigned_to_nat(3u);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 3, v_r_1652_);
lean_ctor_set(v___x_1674_, 2, v_v_1067_);
lean_ctor_set(v___x_1674_, 1, v_k_1066_);
lean_ctor_set(v___x_1674_, 0, v___x_1560_);
v___x_1678_ = v___x_1674_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v_r_1652_);
lean_ctor_set(v_reuseFailAlloc_1682_, 4, v_r_1652_);
v___x_1678_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v___x_1678_);
lean_ctor_set(v___x_1071_, 3, v_l_1651_);
lean_ctor_set(v___x_1071_, 2, v_v_1672_);
lean_ctor_set(v___x_1071_, 1, v_k_1671_);
lean_ctor_set(v___x_1071_, 0, v___x_1676_);
v___x_1680_ = v___x_1071_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_k_1671_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_v_1672_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_l_1651_);
lean_ctor_set(v_reuseFailAlloc_1681_, 4, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
else
{
lean_object* v_r_1687_; 
v_r_1687_ = lean_ctor_get(v_l_1068_, 4);
lean_inc(v_r_1687_);
if (lean_obj_tag(v_r_1687_) == 0)
{
lean_object* v_k_1688_; lean_object* v_v_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1712_; 
lean_inc(v_l_1651_);
v_k_1688_ = lean_ctor_get(v_l_1068_, 1);
v_v_1689_ = lean_ctor_get(v_l_1068_, 2);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_l_1068_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; lean_object* v_unused_1714_; lean_object* v_unused_1715_; 
v_unused_1713_ = lean_ctor_get(v_l_1068_, 4);
lean_dec(v_unused_1713_);
v_unused_1714_ = lean_ctor_get(v_l_1068_, 3);
lean_dec(v_unused_1714_);
v_unused_1715_ = lean_ctor_get(v_l_1068_, 0);
lean_dec(v_unused_1715_);
v___x_1691_ = v_l_1068_;
v_isShared_1692_ = v_isSharedCheck_1712_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_v_1689_);
lean_inc(v_k_1688_);
lean_dec(v_l_1068_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1712_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v_k_1693_; lean_object* v_v_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1708_; 
v_k_1693_ = lean_ctor_get(v_r_1687_, 1);
v_v_1694_ = lean_ctor_get(v_r_1687_, 2);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_r_1687_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; lean_object* v_unused_1710_; lean_object* v_unused_1711_; 
v_unused_1709_ = lean_ctor_get(v_r_1687_, 4);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v_r_1687_, 3);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v_r_1687_, 0);
lean_dec(v_unused_1711_);
v___x_1696_ = v_r_1687_;
v_isShared_1697_ = v_isSharedCheck_1708_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_v_1694_);
lean_inc(v_k_1693_);
lean_dec(v_r_1687_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1708_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = lean_unsigned_to_nat(3u);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 4, v_l_1651_);
lean_ctor_set(v___x_1696_, 3, v_l_1651_);
lean_ctor_set(v___x_1696_, 2, v_v_1689_);
lean_ctor_set(v___x_1696_, 1, v_k_1688_);
lean_ctor_set(v___x_1696_, 0, v___x_1560_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_k_1688_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_v_1689_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_l_1651_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_l_1651_);
v___x_1700_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1702_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 4, v_l_1651_);
lean_ctor_set(v___x_1691_, 2, v_v_1067_);
lean_ctor_set(v___x_1691_, 1, v_k_1066_);
lean_ctor_set(v___x_1691_, 0, v___x_1560_);
v___x_1702_ = v___x_1691_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_l_1651_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v_l_1651_);
v___x_1702_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1704_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v___x_1702_);
lean_ctor_set(v___x_1071_, 3, v___x_1700_);
lean_ctor_set(v___x_1071_, 2, v_v_1694_);
lean_ctor_set(v___x_1071_, 1, v_k_1693_);
lean_ctor_set(v___x_1071_, 0, v___x_1698_);
v___x_1704_ = v___x_1071_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_k_1693_);
lean_ctor_set(v_reuseFailAlloc_1705_, 2, v_v_1694_);
lean_ctor_set(v_reuseFailAlloc_1705_, 3, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1705_, 4, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = lean_unsigned_to_nat(2u);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v_r_1687_);
lean_ctor_set(v___x_1071_, 0, v___x_1716_);
v___x_1718_ = v___x_1071_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1719_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1719_, 3, v_l_1068_);
lean_ctor_set(v_reuseFailAlloc_1719_, 4, v_r_1687_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v___x_1721_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v_l_1068_);
lean_ctor_set(v___x_1071_, 0, v___x_1560_);
v___x_1721_ = v___x_1071_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_k_1066_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_v_1067_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_l_1068_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_l_1068_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
}
}
else
{
return v_t_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_1725_, lean_object* v_t_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1725_, v_t_1726_);
lean_dec(v_k_1725_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_1728_, lean_object* v_declName_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v_ext_1734_; lean_object* v_toEnvExtension_1735_; lean_object* v_env_1736_; lean_object* v_asyncMode_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___y_1741_; lean_object* v_funCC_1767_; uint8_t v___x_1768_; 
v___x_1733_ = lean_st_ref_get(v_a_1731_);
v_ext_1734_ = lean_ctor_get(v_ext_1728_, 1);
v_toEnvExtension_1735_ = lean_ctor_get(v_ext_1734_, 0);
v_env_1736_ = lean_ctor_get(v___x_1733_, 0);
lean_inc_ref(v_env_1736_);
lean_dec(v___x_1733_);
v_asyncMode_1737_ = lean_ctor_get(v_toEnvExtension_1735_, 2);
v___x_1738_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1739_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1738_, v_ext_1728_, v_env_1736_, v_asyncMode_1737_);
v_funCC_1767_ = lean_ctor_get(v___x_1739_, 2);
lean_inc(v_funCC_1767_);
v___x_1768_ = l_Lean_NameSet_contains(v_funCC_1767_, v_declName_1729_);
lean_dec(v_funCC_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; 
lean_inc(v_declName_1729_);
v___x_1769_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_dec_ref_known(v___x_1769_, 1);
v___y_1741_ = v_a_1731_;
goto v___jp_1740_;
}
else
{
lean_dec(v___x_1739_);
lean_dec(v_declName_1729_);
lean_dec_ref(v_ext_1728_);
return v___x_1769_;
}
}
else
{
v___y_1741_ = v_a_1731_;
goto v___jp_1740_;
}
v___jp_1740_:
{
lean_object* v_funCC_1742_; lean_object* v___x_1743_; lean_object* v_env_1744_; lean_object* v_nextMacroScope_1745_; lean_object* v_ngen_1746_; lean_object* v_auxDeclNGen_1747_; lean_object* v_traceState_1748_; lean_object* v_messages_1749_; lean_object* v_infoState_1750_; lean_object* v_snapshotTasks_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1765_; 
v_funCC_1742_ = lean_ctor_get(v___x_1739_, 2);
lean_inc(v_funCC_1742_);
lean_dec(v___x_1739_);
v___x_1743_ = lean_st_ref_take(v___y_1741_);
v_env_1744_ = lean_ctor_get(v___x_1743_, 0);
v_nextMacroScope_1745_ = lean_ctor_get(v___x_1743_, 1);
v_ngen_1746_ = lean_ctor_get(v___x_1743_, 2);
v_auxDeclNGen_1747_ = lean_ctor_get(v___x_1743_, 3);
v_traceState_1748_ = lean_ctor_get(v___x_1743_, 4);
v_messages_1749_ = lean_ctor_get(v___x_1743_, 6);
v_infoState_1750_ = lean_ctor_get(v___x_1743_, 7);
v_snapshotTasks_1751_ = lean_ctor_get(v___x_1743_, 8);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1743_, 5);
lean_dec(v_unused_1766_);
v___x_1753_ = v___x_1743_;
v_isShared_1754_ = v_isSharedCheck_1765_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_snapshotTasks_1751_);
lean_inc(v_infoState_1750_);
lean_inc(v_messages_1749_);
lean_inc(v_traceState_1748_);
lean_inc(v_auxDeclNGen_1747_);
lean_inc(v_ngen_1746_);
lean_inc(v_nextMacroScope_1745_);
lean_inc(v_env_1744_);
lean_dec(v___x_1743_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1765_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___f_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1755_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_1729_, v_funCC_1742_);
lean_dec(v_declName_1729_);
v___f_1756_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_1756_, 0, v___x_1755_);
v___x_1757_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1728_, v_env_1744_, v___f_1756_);
v___x_1758_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 5, v___x_1758_);
lean_ctor_set(v___x_1753_, 0, v___x_1757_);
v___x_1760_ = v___x_1753_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_nextMacroScope_1745_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_ngen_1746_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_auxDeclNGen_1747_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v_traceState_1748_);
lean_ctor_set(v_reuseFailAlloc_1764_, 5, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1764_, 6, v_messages_1749_);
lean_ctor_set(v_reuseFailAlloc_1764_, 7, v_infoState_1750_);
lean_ctor_set(v_reuseFailAlloc_1764_, 8, v_snapshotTasks_1751_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_st_ref_set(v___y_1741_, v___x_1760_);
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_1770_, lean_object* v_declName_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1770_, v_declName_1771_, v_a_1772_, v_a_1773_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_1776_, lean_object* v_k_1777_, lean_object* v_t_1778_, lean_object* v_h_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1777_, v_t_1778_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_1781_, lean_object* v_k_1782_, lean_object* v_t_1783_, lean_object* v_h_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_1781_, v_k_1782_, v_t_1783_, v_h_1784_);
lean_dec(v_k_1782_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_1786_, lean_object* v_s_1787_){
_start:
{
lean_object* v_casesTypes_1788_; lean_object* v_extThms_1789_; lean_object* v_funCC_1790_; lean_object* v_inj_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_casesTypes_1788_ = lean_ctor_get(v_s_1787_, 0);
v_extThms_1789_ = lean_ctor_get(v_s_1787_, 1);
v_funCC_1790_ = lean_ctor_get(v_s_1787_, 2);
v_inj_1791_ = lean_ctor_get(v_s_1787_, 4);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_s_1787_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v_s_1787_, 3);
lean_dec(v_unused_1799_);
v___x_1793_ = v_s_1787_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_inj_1791_);
lean_inc(v_funCC_1790_);
lean_inc(v_extThms_1789_);
lean_inc(v_casesTypes_1788_);
lean_dec(v_s_1787_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 3, v_a_1786_);
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_casesTypes_1788_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_extThms_1789_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_funCC_1790_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v_a_1786_);
lean_ctor_set(v_reuseFailAlloc_1797_, 4, v_inj_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_1801_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
lean_ctor_set(v___x_1801_, 2, v___x_1800_);
lean_ctor_set(v___x_1801_, 3, v___x_1800_);
lean_ctor_set(v___x_1801_, 4, v___x_1800_);
lean_ctor_set(v___x_1801_, 5, v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_1802_, lean_object* v_declName_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v___x_1809_; lean_object* v_ext_1810_; lean_object* v_toEnvExtension_1811_; lean_object* v_env_1812_; lean_object* v_asyncMode_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v_ematch_1816_; lean_object* v___x_1817_; 
v___x_1809_ = lean_st_ref_get(v_a_1807_);
v_ext_1810_ = lean_ctor_get(v_ext_1802_, 1);
v_toEnvExtension_1811_ = lean_ctor_get(v_ext_1810_, 0);
v_env_1812_ = lean_ctor_get(v___x_1809_, 0);
lean_inc_ref(v_env_1812_);
lean_dec(v___x_1809_);
v_asyncMode_1813_ = lean_ctor_get(v_toEnvExtension_1811_, 2);
v___x_1814_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1815_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1814_, v_ext_1802_, v_env_1812_, v_asyncMode_1813_);
v_ematch_1816_ = lean_ctor_get(v___x_1815_, 3);
lean_inc_ref(v_ematch_1816_);
lean_dec(v___x_1815_);
v___x_1817_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_1816_, v_declName_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1862_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1862_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1862_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v_env_1823_; lean_object* v_nextMacroScope_1824_; lean_object* v_ngen_1825_; lean_object* v_auxDeclNGen_1826_; lean_object* v_traceState_1827_; lean_object* v_messages_1828_; lean_object* v_infoState_1829_; lean_object* v_snapshotTasks_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1860_; 
v___x_1822_ = lean_st_ref_take(v_a_1807_);
v_env_1823_ = lean_ctor_get(v___x_1822_, 0);
v_nextMacroScope_1824_ = lean_ctor_get(v___x_1822_, 1);
v_ngen_1825_ = lean_ctor_get(v___x_1822_, 2);
v_auxDeclNGen_1826_ = lean_ctor_get(v___x_1822_, 3);
v_traceState_1827_ = lean_ctor_get(v___x_1822_, 4);
v_messages_1828_ = lean_ctor_get(v___x_1822_, 6);
v_infoState_1829_ = lean_ctor_get(v___x_1822_, 7);
v_snapshotTasks_1830_ = lean_ctor_get(v___x_1822_, 8);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v___x_1822_, 5);
lean_dec(v_unused_1861_);
v___x_1832_ = v___x_1822_;
v_isShared_1833_ = v_isSharedCheck_1860_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_snapshotTasks_1830_);
lean_inc(v_infoState_1829_);
lean_inc(v_messages_1828_);
lean_inc(v_traceState_1827_);
lean_inc(v_auxDeclNGen_1826_);
lean_inc(v_ngen_1825_);
lean_inc(v_nextMacroScope_1824_);
lean_inc(v_env_1823_);
lean_dec(v___x_1822_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1860_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___f_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___f_1834_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_1834_, 0, v_a_1818_);
v___x_1835_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1802_, v_env_1823_, v___f_1834_);
v___x_1836_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 5, v___x_1836_);
lean_ctor_set(v___x_1832_, 0, v___x_1835_);
v___x_1838_ = v___x_1832_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_nextMacroScope_1824_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_ngen_1825_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_auxDeclNGen_1826_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_traceState_1827_);
lean_ctor_set(v_reuseFailAlloc_1859_, 5, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1859_, 6, v_messages_1828_);
lean_ctor_set(v_reuseFailAlloc_1859_, 7, v_infoState_1829_);
lean_ctor_set(v_reuseFailAlloc_1859_, 8, v_snapshotTasks_1830_);
v___x_1838_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v_mctx_1841_; lean_object* v_zetaDeltaFVarIds_1842_; lean_object* v_postponed_1843_; lean_object* v_diag_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1857_; 
v___x_1839_ = lean_st_ref_set(v_a_1807_, v___x_1838_);
v___x_1840_ = lean_st_ref_take(v_a_1805_);
v_mctx_1841_ = lean_ctor_get(v___x_1840_, 0);
v_zetaDeltaFVarIds_1842_ = lean_ctor_get(v___x_1840_, 2);
v_postponed_1843_ = lean_ctor_get(v___x_1840_, 3);
v_diag_1844_ = lean_ctor_get(v___x_1840_, 4);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1840_, 1);
lean_dec(v_unused_1858_);
v___x_1846_ = v___x_1840_;
v_isShared_1847_ = v_isSharedCheck_1857_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_diag_1844_);
lean_inc(v_postponed_1843_);
lean_inc(v_zetaDeltaFVarIds_1842_);
lean_inc(v_mctx_1841_);
lean_dec(v___x_1840_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1857_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___x_1848_);
v___x_1850_ = v___x_1846_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_mctx_1841_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_zetaDeltaFVarIds_1842_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v_postponed_1843_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v_diag_1844_);
v___x_1850_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1851_ = lean_st_ref_set(v_a_1805_, v___x_1850_);
v___x_1852_ = lean_box(0);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1852_);
v___x_1854_ = v___x_1820_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v_ext_1802_);
v_a_1863_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1817_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1817_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_1871_, lean_object* v_declName_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1871_, v_declName_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_1879_, lean_object* v_s_1880_){
_start:
{
lean_object* v_casesTypes_1881_; lean_object* v_extThms_1882_; lean_object* v_funCC_1883_; lean_object* v_ematch_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
v_casesTypes_1881_ = lean_ctor_get(v_s_1880_, 0);
v_extThms_1882_ = lean_ctor_get(v_s_1880_, 1);
v_funCC_1883_ = lean_ctor_get(v_s_1880_, 2);
v_ematch_1884_ = lean_ctor_get(v_s_1880_, 3);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_s_1880_);
if (v_isSharedCheck_1891_ == 0)
{
lean_object* v_unused_1892_; 
v_unused_1892_ = lean_ctor_get(v_s_1880_, 4);
lean_dec(v_unused_1892_);
v___x_1886_ = v_s_1880_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_ematch_1884_);
lean_inc(v_funCC_1883_);
lean_inc(v_extThms_1882_);
lean_inc(v_casesTypes_1881_);
lean_dec(v_s_1880_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 4, v_a_1879_);
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_casesTypes_1881_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_extThms_1882_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_funCC_1883_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_ematch_1884_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v_a_1879_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_1893_, lean_object* v_declName_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v_ext_1901_; lean_object* v_toEnvExtension_1902_; lean_object* v_env_1903_; lean_object* v_asyncMode_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_inj_1907_; lean_object* v___x_1908_; 
v___x_1900_ = lean_st_ref_get(v_a_1898_);
v_ext_1901_ = lean_ctor_get(v_ext_1893_, 1);
v_toEnvExtension_1902_ = lean_ctor_get(v_ext_1901_, 0);
v_env_1903_ = lean_ctor_get(v___x_1900_, 0);
lean_inc_ref(v_env_1903_);
lean_dec(v___x_1900_);
v_asyncMode_1904_ = lean_ctor_get(v_toEnvExtension_1902_, 2);
v___x_1905_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1906_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1905_, v_ext_1893_, v_env_1903_, v_asyncMode_1904_);
v_inj_1907_ = lean_ctor_get(v___x_1906_, 4);
lean_inc_ref(v_inj_1907_);
lean_dec(v___x_1906_);
v___x_1908_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_1907_, v_declName_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1953_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1953_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1953_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v_env_1914_; lean_object* v_nextMacroScope_1915_; lean_object* v_ngen_1916_; lean_object* v_auxDeclNGen_1917_; lean_object* v_traceState_1918_; lean_object* v_messages_1919_; lean_object* v_infoState_1920_; lean_object* v_snapshotTasks_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1951_; 
v___x_1913_ = lean_st_ref_take(v_a_1898_);
v_env_1914_ = lean_ctor_get(v___x_1913_, 0);
v_nextMacroScope_1915_ = lean_ctor_get(v___x_1913_, 1);
v_ngen_1916_ = lean_ctor_get(v___x_1913_, 2);
v_auxDeclNGen_1917_ = lean_ctor_get(v___x_1913_, 3);
v_traceState_1918_ = lean_ctor_get(v___x_1913_, 4);
v_messages_1919_ = lean_ctor_get(v___x_1913_, 6);
v_infoState_1920_ = lean_ctor_get(v___x_1913_, 7);
v_snapshotTasks_1921_ = lean_ctor_get(v___x_1913_, 8);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v___x_1913_, 5);
lean_dec(v_unused_1952_);
v___x_1923_ = v___x_1913_;
v_isShared_1924_ = v_isSharedCheck_1951_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_snapshotTasks_1921_);
lean_inc(v_infoState_1920_);
lean_inc(v_messages_1919_);
lean_inc(v_traceState_1918_);
lean_inc(v_auxDeclNGen_1917_);
lean_inc(v_ngen_1916_);
lean_inc(v_nextMacroScope_1915_);
lean_inc(v_env_1914_);
lean_dec(v___x_1913_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1951_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___f_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___f_1925_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_1925_, 0, v_a_1909_);
v___x_1926_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1893_, v_env_1914_, v___f_1925_);
v___x_1927_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 5, v___x_1927_);
lean_ctor_set(v___x_1923_, 0, v___x_1926_);
v___x_1929_ = v___x_1923_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_nextMacroScope_1915_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v_ngen_1916_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v_auxDeclNGen_1917_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v_traceState_1918_);
lean_ctor_set(v_reuseFailAlloc_1950_, 5, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_1950_, 6, v_messages_1919_);
lean_ctor_set(v_reuseFailAlloc_1950_, 7, v_infoState_1920_);
lean_ctor_set(v_reuseFailAlloc_1950_, 8, v_snapshotTasks_1921_);
v___x_1929_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v_mctx_1932_; lean_object* v_zetaDeltaFVarIds_1933_; lean_object* v_postponed_1934_; lean_object* v_diag_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1948_; 
v___x_1930_ = lean_st_ref_set(v_a_1898_, v___x_1929_);
v___x_1931_ = lean_st_ref_take(v_a_1896_);
v_mctx_1932_ = lean_ctor_get(v___x_1931_, 0);
v_zetaDeltaFVarIds_1933_ = lean_ctor_get(v___x_1931_, 2);
v_postponed_1934_ = lean_ctor_get(v___x_1931_, 3);
v_diag_1935_ = lean_ctor_get(v___x_1931_, 4);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1948_ == 0)
{
lean_object* v_unused_1949_; 
v_unused_1949_ = lean_ctor_get(v___x_1931_, 1);
lean_dec(v_unused_1949_);
v___x_1937_ = v___x_1931_;
v_isShared_1938_ = v_isSharedCheck_1948_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_diag_1935_);
lean_inc(v_postponed_1934_);
lean_inc(v_zetaDeltaFVarIds_1933_);
lean_inc(v_mctx_1932_);
lean_dec(v___x_1931_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1948_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 1, v___x_1939_);
v___x_1941_ = v___x_1937_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_mctx_1932_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_zetaDeltaFVarIds_1933_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_postponed_1934_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_diag_1935_);
v___x_1941_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1942_ = lean_st_ref_set(v_a_1896_, v___x_1941_);
v___x_1943_ = lean_box(0);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1943_);
v___x_1945_ = v___x_1911_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v_ext_1893_);
v_a_1954_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1908_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1908_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_1962_, lean_object* v_declName_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_1962_, v_declName_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
return v_res_1969_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1970_, lean_object* v_i_1971_, lean_object* v_k_1972_){
_start:
{
lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = lean_array_get_size(v_keys_1970_);
v___x_1974_ = lean_nat_dec_lt(v_i_1971_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_dec(v_i_1971_);
return v___x_1974_;
}
else
{
lean_object* v_k_x27_1975_; uint8_t v___x_1976_; 
v_k_x27_1975_ = lean_array_fget_borrowed(v_keys_1970_, v_i_1971_);
v___x_1976_ = lean_name_eq(v_k_1972_, v_k_x27_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_unsigned_to_nat(1u);
v___x_1978_ = lean_nat_add(v_i_1971_, v___x_1977_);
lean_dec(v_i_1971_);
v_i_1971_ = v___x_1978_;
goto _start;
}
else
{
lean_dec(v_i_1971_);
return v___x_1976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1980_, lean_object* v_i_1981_, lean_object* v_k_1982_){
_start:
{
uint8_t v_res_1983_; lean_object* v_r_1984_; 
v_res_1983_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_1980_, v_i_1981_, v_k_1982_);
lean_dec(v_k_1982_);
lean_dec_ref(v_keys_1980_);
v_r_1984_ = lean_box(v_res_1983_);
return v_r_1984_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_1985_, size_t v_x_1986_, lean_object* v_x_1987_){
_start:
{
if (lean_obj_tag(v_x_1985_) == 0)
{
lean_object* v_es_1988_; lean_object* v___x_1989_; size_t v___x_1990_; size_t v___x_1991_; lean_object* v_j_1992_; lean_object* v___x_1993_; 
v_es_1988_ = lean_ctor_get(v_x_1985_, 0);
v___x_1989_ = lean_box(2);
v___x_1990_ = ((size_t)31ULL);
v___x_1991_ = lean_usize_land(v_x_1986_, v___x_1990_);
v_j_1992_ = lean_usize_to_nat(v___x_1991_);
v___x_1993_ = lean_array_get_borrowed(v___x_1989_, v_es_1988_, v_j_1992_);
lean_dec(v_j_1992_);
switch(lean_obj_tag(v___x_1993_))
{
case 0:
{
lean_object* v_key_1994_; uint8_t v___x_1995_; 
v_key_1994_ = lean_ctor_get(v___x_1993_, 0);
v___x_1995_ = lean_name_eq(v_x_1987_, v_key_1994_);
return v___x_1995_;
}
case 1:
{
lean_object* v_node_1996_; size_t v___x_1997_; size_t v___x_1998_; 
v_node_1996_ = lean_ctor_get(v___x_1993_, 0);
v___x_1997_ = ((size_t)5ULL);
v___x_1998_ = lean_usize_shift_right(v_x_1986_, v___x_1997_);
v_x_1985_ = v_node_1996_;
v_x_1986_ = v___x_1998_;
goto _start;
}
default: 
{
uint8_t v___x_2000_; 
v___x_2000_ = 0;
return v___x_2000_;
}
}
}
else
{
lean_object* v_ks_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_ks_2001_ = lean_ctor_get(v_x_1985_, 0);
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_2001_, v___x_2002_, v_x_1987_);
return v___x_2003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_){
_start:
{
size_t v_x_327__boxed_2007_; uint8_t v_res_2008_; lean_object* v_r_2009_; 
v_x_327__boxed_2007_ = lean_unbox_usize(v_x_2005_);
lean_dec(v_x_2005_);
v_res_2008_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2004_, v_x_327__boxed_2007_, v_x_2006_);
lean_dec(v_x_2006_);
lean_dec_ref(v_x_2004_);
v_r_2009_ = lean_box(v_res_2008_);
return v_r_2009_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2010_; uint64_t v___x_2011_; 
v___x_2010_ = lean_unsigned_to_nat(1723u);
v___x_2011_ = lean_uint64_of_nat(v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_2012_, lean_object* v_x_2013_){
_start:
{
uint64_t v___y_2015_; 
if (lean_obj_tag(v_x_2013_) == 0)
{
uint64_t v___x_2018_; 
v___x_2018_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_2015_ = v___x_2018_;
goto v___jp_2014_;
}
else
{
uint64_t v_hash_2019_; 
v_hash_2019_ = lean_ctor_get_uint64(v_x_2013_, sizeof(void*)*2);
v___y_2015_ = v_hash_2019_;
goto v___jp_2014_;
}
v___jp_2014_:
{
size_t v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = lean_uint64_to_usize(v___y_2015_);
v___x_2017_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2012_, v___x_2016_, v_x_2013_);
return v___x_2017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
uint8_t v_res_2022_; lean_object* v_r_2023_; 
v_res_2022_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2020_, v_x_2021_);
lean_dec(v_x_2021_);
lean_dec_ref(v_x_2020_);
v_r_2023_ = lean_box(v_res_2022_);
return v_r_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_2024_, lean_object* v_declName_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v___x_2028_; lean_object* v_ext_2029_; lean_object* v_toEnvExtension_2030_; lean_object* v_env_2031_; lean_object* v_asyncMode_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v_extThms_2035_; uint8_t v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2028_ = lean_st_ref_get(v_a_2026_);
v_ext_2029_ = lean_ctor_get(v_ext_2024_, 1);
v_toEnvExtension_2030_ = lean_ctor_get(v_ext_2029_, 0);
v_env_2031_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_ref(v_env_2031_);
lean_dec(v___x_2028_);
v_asyncMode_2032_ = lean_ctor_get(v_toEnvExtension_2030_, 2);
v___x_2033_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2034_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2033_, v_ext_2024_, v_env_2031_, v_asyncMode_2032_);
v_extThms_2035_ = lean_ctor_get(v___x_2034_, 1);
lean_inc_ref(v_extThms_2035_);
lean_dec(v___x_2034_);
v___x_2036_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_2035_, v_declName_2025_);
lean_dec_ref(v_extThms_2035_);
v___x_2037_ = lean_box(v___x_2036_);
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_2039_, lean_object* v_declName_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2039_, v_declName_2040_, v_a_2041_);
lean_dec(v_a_2041_);
lean_dec(v_declName_2040_);
lean_dec_ref(v_ext_2039_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_2044_, lean_object* v_declName_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2044_, v_declName_2045_, v_a_2047_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_2050_, lean_object* v_declName_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2050_, v_declName_2051_, v_a_2052_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_declName_2051_);
lean_dec_ref(v_ext_2050_);
return v_res_2055_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_){
_start:
{
uint8_t v___x_2059_; 
v___x_2059_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2057_, v_x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_2060_, lean_object* v_x_2061_, lean_object* v_x_2062_){
_start:
{
uint8_t v_res_2063_; lean_object* v_r_2064_; 
v_res_2063_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_2060_, v_x_2061_, v_x_2062_);
lean_dec(v_x_2062_);
lean_dec_ref(v_x_2061_);
v_r_2064_ = lean_box(v_res_2063_);
return v_r_2064_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_2065_, lean_object* v_x_2066_, size_t v_x_2067_, lean_object* v_x_2068_){
_start:
{
uint8_t v___x_2069_; 
v___x_2069_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2066_, v_x_2067_, v_x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_){
_start:
{
size_t v_x_418__boxed_2074_; uint8_t v_res_2075_; lean_object* v_r_2076_; 
v_x_418__boxed_2074_ = lean_unbox_usize(v_x_2072_);
lean_dec(v_x_2072_);
v_res_2075_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2070_, v_x_2071_, v_x_418__boxed_2074_, v_x_2073_);
lean_dec(v_x_2073_);
lean_dec_ref(v_x_2071_);
v_r_2076_ = lean_box(v_res_2075_);
return v_r_2076_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2077_, lean_object* v_keys_2078_, lean_object* v_vals_2079_, lean_object* v_heq_2080_, lean_object* v_i_2081_, lean_object* v_k_2082_){
_start:
{
uint8_t v___x_2083_; 
v___x_2083_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2078_, v_i_2081_, v_k_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2084_, lean_object* v_keys_2085_, lean_object* v_vals_2086_, lean_object* v_heq_2087_, lean_object* v_i_2088_, lean_object* v_k_2089_){
_start:
{
uint8_t v_res_2090_; lean_object* v_r_2091_; 
v_res_2090_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_2084_, v_keys_2085_, v_vals_2086_, v_heq_2087_, v_i_2088_, v_k_2089_);
lean_dec(v_k_2089_);
lean_dec_ref(v_vals_2086_);
lean_dec_ref(v_keys_2085_);
v_r_2091_ = lean_box(v_res_2090_);
return v_r_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_2092_, lean_object* v_declName_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v___x_2096_; lean_object* v_ext_2097_; lean_object* v_toEnvExtension_2098_; lean_object* v_env_2099_; lean_object* v_asyncMode_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v_inj_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2096_ = lean_st_ref_get(v_a_2094_);
v_ext_2097_ = lean_ctor_get(v_ext_2092_, 1);
v_toEnvExtension_2098_ = lean_ctor_get(v_ext_2097_, 0);
v_env_2099_ = lean_ctor_get(v___x_2096_, 0);
lean_inc_ref(v_env_2099_);
lean_dec(v___x_2096_);
v_asyncMode_2100_ = lean_ctor_get(v_toEnvExtension_2098_, 2);
v___x_2101_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2102_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2101_, v_ext_2092_, v_env_2099_, v_asyncMode_2100_);
v_inj_2103_ = lean_ctor_get(v___x_2102_, 4);
lean_inc_ref(v_inj_2103_);
lean_dec(v___x_2102_);
v___x_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2104_, 0, v_declName_2093_);
v___x_2105_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_2103_, v___x_2104_);
lean_dec_ref_known(v___x_2104_, 1);
lean_dec_ref(v_inj_2103_);
v___x_2106_ = lean_box(v___x_2105_);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_2108_, lean_object* v_declName_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2108_, v_declName_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec_ref(v_ext_2108_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_2113_, lean_object* v_declName_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2113_, v_declName_2114_, v_a_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_2119_, lean_object* v_declName_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2119_, v_declName_2120_, v_a_2121_, v_a_2122_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec_ref(v_ext_2119_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_2125_, lean_object* v_declName_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v___x_2129_; lean_object* v_ext_2130_; lean_object* v_toEnvExtension_2131_; lean_object* v_env_2132_; lean_object* v_asyncMode_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v_funCC_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2129_ = lean_st_ref_get(v_a_2127_);
v_ext_2130_ = lean_ctor_get(v_ext_2125_, 1);
v_toEnvExtension_2131_ = lean_ctor_get(v_ext_2130_, 0);
v_env_2132_ = lean_ctor_get(v___x_2129_, 0);
lean_inc_ref(v_env_2132_);
lean_dec(v___x_2129_);
v_asyncMode_2133_ = lean_ctor_get(v_toEnvExtension_2131_, 2);
v___x_2134_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2135_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2134_, v_ext_2125_, v_env_2132_, v_asyncMode_2133_);
v_funCC_2136_ = lean_ctor_get(v___x_2135_, 2);
lean_inc(v_funCC_2136_);
lean_dec(v___x_2135_);
v___x_2137_ = l_Lean_NameSet_contains(v_funCC_2136_, v_declName_2126_);
lean_dec(v_funCC_2136_);
v___x_2138_ = lean_box(v___x_2137_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_2140_, lean_object* v_declName_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2140_, v_declName_2141_, v_a_2142_);
lean_dec(v_a_2142_);
lean_dec(v_declName_2141_);
lean_dec_ref(v_ext_2140_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_2145_, lean_object* v_declName_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2145_, v_declName_2146_, v_a_2148_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_2151_, lean_object* v_declName_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2151_, v_declName_2152_, v_a_2153_, v_a_2154_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec(v_declName_2152_);
lean_dec_ref(v_ext_2151_);
return v_res_2156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_2181_ = l_Lean_mkAtom(v___x_2180_);
return v___x_2181_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_2183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2184_ = lean_array_push(v___x_2183_, v___x_2182_);
return v___x_2184_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_2194_ = l_Lean_mkAtom(v___x_2193_);
return v___x_2194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_2196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2197_ = lean_array_push(v___x_2196_, v___x_2195_);
return v___x_2197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_2199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_2200_ = lean_box(2);
v___x_2201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v___x_2199_);
lean_ctor_set(v___x_2201_, 2, v___x_2198_);
return v___x_2201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_2203_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_2204_ = lean_array_push(v___x_2203_, v___x_2202_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_2206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_2207_ = lean_box(2);
v___x_2208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2206_);
lean_ctor_set(v___x_2208_, 2, v___x_2205_);
return v___x_2208_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_2210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2211_ = lean_array_push(v___x_2210_, v___x_2209_);
return v___x_2211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_2213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_2214_ = lean_box(2);
v___x_2215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___x_2213_);
lean_ctor_set(v___x_2215_, 2, v___x_2212_);
return v___x_2215_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_2217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2218_ = lean_array_push(v___x_2217_, v___x_2216_);
return v___x_2218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_2220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_2221_ = lean_box(2);
v___x_2222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___x_2220_);
lean_ctor_set(v___x_2222_, 2, v___x_2219_);
return v___x_2222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_2224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2225_ = lean_array_push(v___x_2224_, v___x_2223_);
return v___x_2225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2226_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_2227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_2228_ = lean_box(2);
v___x_2229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v___x_2227_);
lean_ctor_set(v___x_2229_, 2, v___x_2226_);
return v___x_2229_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_2231_, lean_object* v_ext_2232_, lean_object* v_____r_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
uint8_t v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = 0;
lean_inc(v_declName_2231_);
v___x_2240_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_2231_, v___x_2239_, v___y_2236_, v___y_2237_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; uint8_t v___x_2242_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v___x_2242_ = lean_unbox(v_a_2241_);
lean_dec(v_a_2241_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; lean_object* v_a_2244_; uint8_t v___x_2245_; 
v___x_2243_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2232_, v_declName_2231_, v___y_2237_);
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = lean_unbox(v_a_2244_);
lean_dec(v_a_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v_a_2247_; uint8_t v___x_2248_; 
lean_inc(v_declName_2231_);
v___x_2246_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2232_, v_declName_2231_, v___y_2237_);
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = lean_unbox(v_a_2247_);
lean_dec(v_a_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; lean_object* v_a_2250_; uint8_t v___x_2251_; 
v___x_2249_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2232_, v_declName_2231_, v___y_2237_);
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref(v___x_2249_);
v___x_2251_ = lean_unbox(v_a_2250_);
lean_dec(v_a_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; 
v___x_2252_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_2232_, v_declName_2231_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2252_;
}
else
{
lean_object* v___x_2253_; 
v___x_2253_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2232_, v_declName_2231_, v___y_2236_, v___y_2237_);
return v___x_2253_;
}
}
else
{
lean_object* v___x_2254_; 
v___x_2254_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_2232_, v_declName_2231_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2254_;
}
}
else
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2232_, v_declName_2231_, v___y_2236_, v___y_2237_);
return v___x_2255_;
}
}
else
{
lean_object* v___x_2256_; 
v___x_2256_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2232_, v_declName_2231_, v___y_2236_, v___y_2237_);
return v___x_2256_;
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref(v_ext_2232_);
lean_dec(v_declName_2231_);
v_a_2257_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2240_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2240_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_2265_, lean_object* v_ext_2266_, lean_object* v_____r_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2265_, v_ext_2266_, v_____r_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object* v_msgData_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___x_2280_; lean_object* v_env_2281_; lean_object* v___x_2282_; lean_object* v_mctx_2283_; lean_object* v_lctx_2284_; lean_object* v_options_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2280_ = lean_st_ref_get(v___y_2278_);
v_env_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc_ref(v_env_2281_);
lean_dec(v___x_2280_);
v___x_2282_ = lean_st_ref_get(v___y_2276_);
v_mctx_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc_ref(v_mctx_2283_);
lean_dec(v___x_2282_);
v_lctx_2284_ = lean_ctor_get(v___y_2275_, 2);
v_options_2285_ = lean_ctor_get(v___y_2277_, 2);
lean_inc_ref(v_options_2285_);
lean_inc_ref(v_lctx_2284_);
v___x_2286_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2286_, 0, v_env_2281_);
lean_ctor_set(v___x_2286_, 1, v_mctx_2283_);
lean_ctor_set(v___x_2286_, 2, v_lctx_2284_);
lean_ctor_set(v___x_2286_, 3, v_options_2285_);
v___x_2287_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v_msgData_2274_);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object* v_msgData_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_ref_2302_; lean_object* v___x_2303_; lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2312_; 
v_ref_2302_ = lean_ctor_get(v___y_2299_, 5);
v___x_2303_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2310_; 
lean_inc(v_ref_2302_);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v_ref_2302_);
lean_ctor_set(v___x_2308_, 1, v_a_2304_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set_tag(v___x_2306_, 1);
lean_ctor_set(v___x_2306_, 0, v___x_2308_);
v___x_2310_ = v___x_2306_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
return v_res_2319_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2326_; uint64_t v___x_2327_; 
v___x_2326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2327_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2326_);
return v___x_2327_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2330_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
lean_ctor_set_uint64(v___x_2330_, sizeof(void*)*1, v___x_2328_);
return v___x_2330_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2331_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
return v___x_2333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2334_ = lean_box(1);
v___x_2335_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2336_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v___x_2335_);
lean_ctor_set(v___x_2337_, 2, v___x_2334_);
return v___x_2337_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2341_ = lean_unsigned_to_nat(0u);
v___x_2342_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
lean_ctor_set(v___x_2342_, 2, v___x_2341_);
lean_ctor_set(v___x_2342_, 3, v___x_2341_);
lean_ctor_set(v___x_2342_, 4, v___x_2340_);
lean_ctor_set(v___x_2342_, 5, v___x_2340_);
lean_ctor_set(v___x_2342_, 6, v___x_2340_);
lean_ctor_set(v___x_2342_, 7, v___x_2340_);
lean_ctor_set(v___x_2342_, 8, v___x_2340_);
lean_ctor_set(v___x_2342_, 9, v___x_2340_);
return v___x_2342_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2344_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
lean_ctor_set(v___x_2344_, 2, v___x_2343_);
lean_ctor_set(v___x_2344_, 3, v___x_2343_);
lean_ctor_set(v___x_2344_, 4, v___x_2343_);
lean_ctor_set(v___x_2344_, 5, v___x_2343_);
return v___x_2344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
lean_ctor_set(v___x_2346_, 2, v___x_2345_);
lean_ctor_set(v___x_2346_, 3, v___x_2345_);
lean_ctor_set(v___x_2346_, 4, v___x_2345_);
return v___x_2346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10));
v___x_2349_ = l_Lean_stringToMessageData(v___x_2348_);
return v___x_2349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12));
v___x_2352_ = l_Lean_stringToMessageData(v___x_2351_);
return v___x_2352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14));
v___x_2355_ = l_Lean_stringToMessageData(v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v___x_2356_, lean_object* v_ext_2357_, uint8_t v_showInfo_2358_, lean_object* v_attrName_2359_, lean_object* v_declName_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
uint8_t v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___y_2379_; 
v___x_2364_ = 1;
v___x_2365_ = 0;
v___x_2366_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2367_ = lean_unsigned_to_nat(0u);
v___x_2368_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_2371_ = lean_box(0);
lean_inc(v___x_2356_);
v___x_2372_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2372_, 0, v___x_2366_);
lean_ctor_set(v___x_2372_, 1, v___x_2356_);
lean_ctor_set(v___x_2372_, 2, v___x_2369_);
lean_ctor_set(v___x_2372_, 3, v___x_2370_);
lean_ctor_set(v___x_2372_, 4, v___x_2371_);
lean_ctor_set(v___x_2372_, 5, v___x_2367_);
lean_ctor_set(v___x_2372_, 6, v___x_2371_);
lean_ctor_set_uint8(v___x_2372_, sizeof(void*)*7, v___x_2365_);
lean_ctor_set_uint8(v___x_2372_, sizeof(void*)*7 + 1, v___x_2365_);
lean_ctor_set_uint8(v___x_2372_, sizeof(void*)*7 + 2, v___x_2365_);
lean_ctor_set_uint8(v___x_2372_, sizeof(void*)*7 + 3, v___x_2364_);
v___x_2373_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_2374_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2375_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_2376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2373_);
lean_ctor_set(v___x_2376_, 1, v___x_2374_);
lean_ctor_set(v___x_2376_, 2, v___x_2356_);
lean_ctor_set(v___x_2376_, 3, v___x_2368_);
lean_ctor_set(v___x_2376_, 4, v___x_2375_);
v___x_2377_ = lean_st_mk_ref(v___x_2376_);
if (v_showInfo_2358_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_dec(v_attrName_2359_);
v___x_2389_ = lean_box(0);
v___x_2390_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2360_, v_ext_2357_, v___x_2389_, v___x_2372_, v___x_2377_, v___y_2361_, v___y_2362_);
lean_dec_ref_known(v___x_2372_, 7);
v___y_2379_ = v___x_2390_;
goto v___jp_2378_;
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_dec(v_declName_2360_);
lean_dec_ref(v_ext_2357_);
v___x_2391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11);
v___x_2392_ = l_Lean_MessageData_ofName(v_attrName_2359_);
lean_inc_ref(v___x_2392_);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v___x_2392_);
v___x_2397_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15);
v___x_2398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2398_, v___x_2372_, v___x_2377_, v___y_2361_, v___y_2362_);
lean_dec_ref_known(v___x_2372_, 7);
v___y_2379_ = v___x_2399_;
goto v___jp_2378_;
}
v___jp_2378_:
{
if (lean_obj_tag(v___y_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2388_; 
v_a_2380_ = lean_ctor_get(v___y_2379_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___y_2379_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2382_ = v___y_2379_;
v_isShared_2383_ = v_isSharedCheck_2388_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___y_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2388_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2384_ = lean_st_ref_get(v___x_2377_);
lean_dec(v___x_2377_);
lean_dec(v___x_2384_);
if (v_isShared_2383_ == 0)
{
v___x_2386_ = v___x_2382_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2380_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
else
{
lean_dec(v___x_2377_);
return v___y_2379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v___x_2400_, lean_object* v_ext_2401_, lean_object* v_showInfo_2402_, lean_object* v_attrName_2403_, lean_object* v_declName_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
uint8_t v_showInfo_boxed_2408_; lean_object* v_res_2409_; 
v_showInfo_boxed_2408_ = lean_unbox(v_showInfo_2402_);
v_res_2409_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v___x_2400_, v_ext_2401_, v_showInfo_boxed_2408_, v_attrName_2403_, v_declName_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2412_, uint8_t v_attrKind_2413_, uint8_t v_showInfo_2414_, uint8_t v_minIndexable_2415_, lean_object* v_as_x27_2416_, lean_object* v_b_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
if (lean_obj_tag(v_as_x27_2416_) == 0)
{
lean_object* v___x_2423_; 
lean_dec_ref(v_ext_2412_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v_b_2417_);
return v___x_2423_;
}
else
{
lean_object* v_head_2424_; lean_object* v_tail_2425_; lean_object* v___x_2426_; 
v_head_2424_ = lean_ctor_get(v_as_x27_2416_, 0);
v_tail_2425_ = lean_ctor_get(v_as_x27_2416_, 1);
v___x_2426_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2421_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2426_, 1);
v___x_2428_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_2424_);
lean_inc_ref(v_ext_2412_);
v___x_2429_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2412_, v_head_2424_, v_attrKind_2413_, v___x_2428_, v_a_2427_, v_showInfo_2414_, v_minIndexable_2415_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v___x_2430_; 
lean_dec_ref_known(v___x_2429_, 1);
v___x_2430_ = lean_box(0);
v_as_x27_2416_ = v_tail_2425_;
v_b_2417_ = v___x_2430_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2412_);
return v___x_2429_;
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec_ref(v_ext_2412_);
v_a_2432_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2426_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2426_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2440_, lean_object* v_attrKind_2441_, lean_object* v_showInfo_2442_, lean_object* v_minIndexable_2443_, lean_object* v_as_x27_2444_, lean_object* v_b_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
uint8_t v_attrKind_boxed_2451_; uint8_t v_showInfo_boxed_2452_; uint8_t v_minIndexable_boxed_2453_; lean_object* v_res_2454_; 
v_attrKind_boxed_2451_ = lean_unbox(v_attrKind_2441_);
v_showInfo_boxed_2452_ = lean_unbox(v_showInfo_2442_);
v_minIndexable_boxed_2453_ = lean_unbox(v_minIndexable_2443_);
v_res_2454_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2440_, v_attrKind_boxed_2451_, v_showInfo_boxed_2452_, v_minIndexable_boxed_2453_, v_as_x27_2444_, v_b_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v_as_x27_2444_);
return v_res_2454_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2457_ = l_Lean_stringToMessageData(v___x_2456_);
return v___x_2457_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_2462_ = l_Lean_stringToMessageData(v___x_2461_);
return v___x_2462_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_2465_ = l_Lean_stringToMessageData(v___x_2464_);
return v___x_2465_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
return v___x_2468_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12));
v___x_2474_ = l_Lean_stringToMessageData(v___x_2473_);
return v___x_2474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14));
v___x_2477_ = l_Lean_stringToMessageData(v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16));
v___x_2480_ = l_Lean_stringToMessageData(v___x_2479_);
return v___x_2480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18));
v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
return v___x_2483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__21(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__20));
v___x_2486_ = l_Lean_stringToMessageData(v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_stx_2487_, lean_object* v_ext_2488_, lean_object* v_declName_2489_, uint8_t v_attrKind_2490_, uint8_t v_showInfo_2491_, uint8_t v_minIndexable_2492_, uint8_t v___x_2493_, lean_object* v_attrName_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2487_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2537_, 1);
switch(lean_obj_tag(v_a_2538_))
{
case 0:
{
lean_object* v_k_2539_; 
lean_dec(v_attrName_2494_);
lean_dec(v_stx_2487_);
v_k_2539_ = lean_ctor_get(v_a_2538_, 0);
lean_inc(v_k_2539_);
lean_dec_ref_known(v_a_2538_, 1);
if (lean_obj_tag(v_k_2539_) == 9)
{
lean_object* v___x_2540_; 
lean_dec(v_declName_2489_);
lean_dec_ref(v_ext_2488_);
v___x_2540_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2497_, v___y_2498_);
return v___x_2540_;
}
else
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2498_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
v___x_2543_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2488_, v_declName_2489_, v_attrKind_2490_, v_k_2539_, v_a_2542_, v_showInfo_2491_, v_minIndexable_2492_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2543_;
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_k_2539_);
lean_dec(v_declName_2489_);
lean_dec_ref(v_ext_2488_);
v_a_2544_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2541_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2541_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2552_; lean_object* v___x_2553_; 
lean_dec(v_attrName_2494_);
lean_dec(v_stx_2487_);
v_eager_2552_ = lean_ctor_get_uint8(v_a_2538_, 0);
lean_dec_ref_known(v_a_2538_, 0);
v___x_2553_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2488_, v_declName_2489_, v_eager_2552_, v_attrKind_2490_, v___y_2497_, v___y_2498_);
return v___x_2553_;
}
case 2:
{
lean_object* v___x_2554_; 
lean_dec(v_stx_2487_);
lean_inc(v_declName_2489_);
v___x_2554_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2489_, v___x_2493_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v___x_2554_, 1);
if (lean_obj_tag(v_a_2555_) == 1)
{
lean_object* v_val_2556_; lean_object* v_ctors_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_dec(v_attrName_2494_);
lean_dec(v_declName_2489_);
v_val_2556_ = lean_ctor_get(v_a_2555_, 0);
lean_inc(v_val_2556_);
lean_dec_ref_known(v_a_2555_, 1);
v_ctors_2557_ = lean_ctor_get(v_val_2556_, 4);
lean_inc(v_ctors_2557_);
lean_dec(v_val_2556_);
v___x_2558_ = lean_box(0);
v___x_2559_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2488_, v_attrKind_2490_, v_showInfo_2491_, v_minIndexable_2492_, v_ctors_2557_, v___x_2558_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v_ctors_2557_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2566_ == 0)
{
lean_object* v_unused_2567_; 
v_unused_2567_ = lean_ctor_get(v___x_2559_, 0);
lean_dec(v_unused_2567_);
v___x_2561_ = v___x_2559_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_dec(v___x_2559_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2558_);
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2558_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
else
{
return v___x_2559_;
}
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec(v_a_2555_);
lean_dec_ref(v_ext_2488_);
v___x_2568_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_2569_ = l_Lean_MessageData_ofName(v_attrName_2494_);
v___x_2570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2568_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_2572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = l_Lean_MessageData_ofConstName(v_declName_2489_, v___x_2493_);
v___x_2574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9);
v___x_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2576_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2577_;
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v_attrName_2494_);
lean_dec(v_declName_2489_);
lean_dec_ref(v_ext_2488_);
v_a_2578_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2554_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2554_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
case 3:
{
lean_object* v___x_2586_; 
lean_dec(v_attrName_2494_);
lean_inc(v_declName_2489_);
v___x_2586_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2489_, v___x_2493_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
if (lean_obj_tag(v_a_2587_) == 1)
{
lean_object* v_val_2588_; lean_object* v___x_2589_; 
lean_dec(v_declName_2489_);
lean_dec(v_stx_2487_);
v_val_2588_ = lean_ctor_get(v_a_2587_, 0);
lean_inc_n(v_val_2588_, 2);
lean_dec_ref_known(v_a_2587_, 1);
lean_inc_ref(v_ext_2488_);
v___x_2589_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2488_, v_val_2588_, v___x_2493_, v_attrKind_2490_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v___x_2590_; 
lean_dec_ref_known(v___x_2589_, 1);
v___x_2590_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2588_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2611_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2611_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2611_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
if (lean_obj_tag(v_a_2591_) == 1)
{
lean_object* v_val_2595_; lean_object* v_ctors_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_del_object(v___x_2593_);
v_val_2595_ = lean_ctor_get(v_a_2591_, 0);
lean_inc(v_val_2595_);
lean_dec_ref_known(v_a_2591_, 1);
v_ctors_2596_ = lean_ctor_get(v_val_2595_, 4);
lean_inc(v_ctors_2596_);
lean_dec(v_val_2595_);
v___x_2597_ = lean_box(0);
v___x_2598_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2488_, v_attrKind_2490_, v_showInfo_2491_, v_minIndexable_2492_, v_ctors_2596_, v___x_2597_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v_ctors_2596_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v___x_2598_, 0);
lean_dec(v_unused_2606_);
v___x_2600_ = v___x_2598_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_dec(v___x_2598_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2597_);
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2597_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
return v___x_2598_;
}
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
lean_dec(v_a_2591_);
lean_dec_ref(v_ext_2488_);
v___x_2607_ = lean_box(0);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2607_);
v___x_2609_ = v___x_2593_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v_ext_2488_);
v_a_2612_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2590_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2590_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_dec(v_val_2588_);
lean_dec_ref(v_ext_2488_);
return v___x_2589_;
}
}
else
{
lean_object* v___x_2620_; 
lean_dec(v_a_2587_);
v___x_2620_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2498_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2622_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2488_, v_stx_2487_, v_declName_2489_, v_attrKind_2490_, v_a_2621_, v_minIndexable_2492_, v_showInfo_2491_, v___x_2493_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2622_;
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_declName_2489_);
lean_dec_ref(v_ext_2488_);
lean_dec(v_stx_2487_);
v_a_2623_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2620_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2620_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec(v_declName_2489_);
lean_dec_ref(v_ext_2488_);
lean_dec(v_stx_2487_);
v_a_2631_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2586_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2586_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
case 4:
{
lean_object* v___x_2639_; 
lean_dec(v_attrName_2494_);
lean_dec(v_stx_2487_);
v___x_2639_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2488_, v_declName_2489_, v_attrKind_2490_, v___y_2497_, v___y_2498_);
return v___x_2639_;
}
case 5:
{
lean_object* v_prio_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
lean_dec_ref(v_ext_2488_);
lean_dec(v_stx_2487_);
v_prio_2640_ = lean_ctor_get(v_a_2538_, 0);
lean_inc(v_prio_2640_);
lean_dec_ref_known(v_a_2538_, 1);
v___x_2641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_2642_ = lean_name_eq(v_attrName_2494_, v___x_2641_);
lean_dec(v_attrName_2494_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_dec(v_prio_2640_);
lean_dec(v_declName_2489_);
v___x_2643_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13);
v___x_2644_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2643_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2644_;
}
else
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2489_, v_attrKind_2490_, v_prio_2640_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2645_;
}
}
case 6:
{
lean_object* v___x_2646_; 
lean_dec(v_attrName_2494_);
lean_dec(v_stx_2487_);
v___x_2646_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2488_, v_declName_2489_, v_attrKind_2490_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2646_;
}
case 7:
{
lean_object* v___x_2647_; 
lean_dec(v_attrName_2494_);
lean_dec(v_stx_2487_);
v___x_2647_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2488_, v_declName_2489_, v_attrKind_2490_, v___y_2497_, v___y_2498_);
return v___x_2647_;
}
case 8:
{
uint8_t v_post_2648_; uint8_t v_inv_2649_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
lean_dec_ref(v_ext_2488_);
lean_dec(v_stx_2487_);
v_post_2648_ = lean_ctor_get_uint8(v_a_2538_, 0);
v_inv_2649_ = lean_ctor_get_uint8(v_a_2538_, 1);
lean_dec_ref_known(v_a_2538_, 0);
v___x_2658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_2659_ = lean_name_eq(v_attrName_2494_, v___x_2658_);
lean_dec(v_attrName_2494_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec(v_declName_2489_);
v___x_2660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15);
v___x_2661_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2660_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2661_;
}
else
{
v___y_2651_ = v___y_2495_;
v___y_2652_ = v___y_2496_;
v___y_2653_ = v___y_2497_;
v___y_2654_ = v___y_2498_;
goto v___jp_2650_;
}
v___jp_2650_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = l_Lean_Meta_Grind_normExt;
v___x_2656_ = lean_unsigned_to_nat(1000u);
v___x_2657_ = l_Lean_Meta_addSimpTheorem(v___x_2655_, v_declName_2489_, v_post_2648_, v_inv_2649_, v_attrKind_2490_, v___x_2656_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
return v___x_2657_;
}
}
case 9:
{
lean_object* v___x_2662_; uint8_t v___x_2663_; 
lean_dec_ref(v_ext_2488_);
lean_dec(v_stx_2487_);
v___x_2662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_2663_ = lean_name_eq(v_attrName_2494_, v___x_2662_);
lean_dec(v_attrName_2494_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_dec(v_declName_2489_);
v___x_2664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17);
v___x_2665_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2664_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2665_;
}
else
{
v___y_2501_ = v___y_2495_;
v___y_2502_ = v___y_2496_;
v___y_2503_ = v___y_2497_;
v___y_2504_ = v___y_2498_;
goto v___jp_2500_;
}
}
case 10:
{
lean_object* v___x_2666_; uint8_t v___x_2667_; 
lean_dec_ref(v_ext_2488_);
lean_dec(v_stx_2487_);
v___x_2666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_2667_ = lean_name_eq(v_attrName_2494_, v___x_2666_);
lean_dec(v_attrName_2494_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec(v_declName_2489_);
v___x_2668_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19);
v___x_2669_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2668_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2669_;
}
else
{
v___y_2529_ = v___y_2495_;
v___y_2530_ = v___y_2496_;
v___y_2531_ = v___y_2497_;
v___y_2532_ = v___y_2498_;
goto v___jp_2528_;
}
}
default: 
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
lean_dec_ref(v_ext_2488_);
lean_dec(v_stx_2487_);
v___x_2670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_2671_ = lean_name_eq(v_attrName_2494_, v___x_2670_);
lean_dec(v_attrName_2494_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_dec(v_declName_2489_);
v___x_2672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__21);
v___x_2673_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2672_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2673_;
}
else
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_2489_, v_attrKind_2490_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_attrName_2494_);
lean_dec(v_declName_2489_);
lean_dec_ref(v_ext_2488_);
lean_dec(v_stx_2487_);
v_a_2675_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2537_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2537_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
v___jp_2500_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = l_Lean_Meta_Grind_normExt;
v___x_2506_ = lean_unsigned_to_nat(1000u);
v___x_2507_ = l_Lean_Meta_addDeclToUnfold(v___x_2505_, v_declName_2489_, v___x_2493_, v___x_2493_, v___x_2506_, v_attrKind_2490_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2519_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2519_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2519_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
uint8_t v___x_2512_; 
v___x_2512_ = lean_unbox(v_a_2508_);
lean_dec(v_a_2508_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_del_object(v___x_2510_);
v___x_2513_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2514_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2513_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2514_;
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2515_ = lean_box(0);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v___x_2515_);
v___x_2517_ = v___x_2510_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
v_a_2520_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2507_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2507_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
v___jp_2528_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2533_ = l_Lean_Meta_Grind_homoExt;
v___x_2534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3));
v___x_2536_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v___x_2533_, v___x_2534_, v_declName_2489_, v_attrKind_2490_, v___x_2535_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
return v___x_2536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_stx_2683_, lean_object* v_ext_2684_, lean_object* v_declName_2685_, lean_object* v_attrKind_2686_, lean_object* v_showInfo_2687_, lean_object* v_minIndexable_2688_, lean_object* v___x_2689_, lean_object* v_attrName_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
uint8_t v_attrKind_boxed_2696_; uint8_t v_showInfo_boxed_2697_; uint8_t v_minIndexable_boxed_2698_; uint8_t v___x_15857__boxed_2699_; lean_object* v_res_2700_; 
v_attrKind_boxed_2696_ = lean_unbox(v_attrKind_2686_);
v_showInfo_boxed_2697_ = lean_unbox(v_showInfo_2687_);
v_minIndexable_boxed_2698_ = lean_unbox(v_minIndexable_2688_);
v___x_15857__boxed_2699_ = lean_unbox(v___x_2689_);
v_res_2700_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_stx_2683_, v_ext_2684_, v_declName_2685_, v_attrKind_boxed_2696_, v_showInfo_boxed_2697_, v_minIndexable_boxed_2698_, v___x_15857__boxed_2699_, v_attrName_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
return v_res_2700_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2701_; double v___x_2702_; 
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = lean_float_of_nat(v___x_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_2706_, lean_object* v_msg_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_ref_2713_; lean_object* v___x_2714_; lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2759_; 
v_ref_2713_ = lean_ctor_get(v___y_2710_, 5);
v___x_2714_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2759_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2759_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v_traceState_2720_; lean_object* v_env_2721_; lean_object* v_nextMacroScope_2722_; lean_object* v_ngen_2723_; lean_object* v_auxDeclNGen_2724_; lean_object* v_cache_2725_; lean_object* v_messages_2726_; lean_object* v_infoState_2727_; lean_object* v_snapshotTasks_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2758_; 
v___x_2719_ = lean_st_ref_take(v___y_2711_);
v_traceState_2720_ = lean_ctor_get(v___x_2719_, 4);
v_env_2721_ = lean_ctor_get(v___x_2719_, 0);
v_nextMacroScope_2722_ = lean_ctor_get(v___x_2719_, 1);
v_ngen_2723_ = lean_ctor_get(v___x_2719_, 2);
v_auxDeclNGen_2724_ = lean_ctor_get(v___x_2719_, 3);
v_cache_2725_ = lean_ctor_get(v___x_2719_, 5);
v_messages_2726_ = lean_ctor_get(v___x_2719_, 6);
v_infoState_2727_ = lean_ctor_get(v___x_2719_, 7);
v_snapshotTasks_2728_ = lean_ctor_get(v___x_2719_, 8);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2730_ = v___x_2719_;
v_isShared_2731_ = v_isSharedCheck_2758_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_snapshotTasks_2728_);
lean_inc(v_infoState_2727_);
lean_inc(v_messages_2726_);
lean_inc(v_cache_2725_);
lean_inc(v_traceState_2720_);
lean_inc(v_auxDeclNGen_2724_);
lean_inc(v_ngen_2723_);
lean_inc(v_nextMacroScope_2722_);
lean_inc(v_env_2721_);
lean_dec(v___x_2719_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2758_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
uint64_t v_tid_2732_; lean_object* v_traces_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2757_; 
v_tid_2732_ = lean_ctor_get_uint64(v_traceState_2720_, sizeof(void*)*1);
v_traces_2733_ = lean_ctor_get(v_traceState_2720_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_traceState_2720_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2735_ = v_traceState_2720_;
v_isShared_2736_ = v_isSharedCheck_2757_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_traces_2733_);
lean_dec(v_traceState_2720_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2757_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; double v___x_2738_; uint8_t v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2737_ = lean_box(0);
v___x_2738_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_2739_ = 0;
v___x_2740_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2741_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2741_, 0, v_cls_2706_);
lean_ctor_set(v___x_2741_, 1, v___x_2737_);
lean_ctor_set(v___x_2741_, 2, v___x_2740_);
lean_ctor_set_float(v___x_2741_, sizeof(void*)*3, v___x_2738_);
lean_ctor_set_float(v___x_2741_, sizeof(void*)*3 + 8, v___x_2738_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*3 + 16, v___x_2739_);
v___x_2742_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_2743_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v_a_2715_);
lean_ctor_set(v___x_2743_, 2, v___x_2742_);
lean_inc(v_ref_2713_);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v_ref_2713_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = l_Lean_PersistentArray_push___redArg(v_traces_2733_, v___x_2744_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2745_);
v___x_2747_ = v___x_2735_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2745_);
lean_ctor_set_uint64(v_reuseFailAlloc_2756_, sizeof(void*)*1, v_tid_2732_);
v___x_2747_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2749_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 4, v___x_2747_);
v___x_2749_ = v___x_2730_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_env_2721_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_nextMacroScope_2722_);
lean_ctor_set(v_reuseFailAlloc_2755_, 2, v_ngen_2723_);
lean_ctor_set(v_reuseFailAlloc_2755_, 3, v_auxDeclNGen_2724_);
lean_ctor_set(v_reuseFailAlloc_2755_, 4, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2755_, 5, v_cache_2725_);
lean_ctor_set(v_reuseFailAlloc_2755_, 6, v_messages_2726_);
lean_ctor_set(v_reuseFailAlloc_2755_, 7, v_infoState_2727_);
lean_ctor_set(v_reuseFailAlloc_2755_, 8, v_snapshotTasks_2728_);
v___x_2749_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2750_ = lean_st_ref_set(v___y_2711_, v___x_2749_);
v___x_2751_ = lean_box(0);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2751_);
v___x_2753_ = v___x_2717_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_2760_, lean_object* v_msg_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2760_, v_msg_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
return v_res_2767_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_2768_, lean_object* v_i_2769_, lean_object* v_k_2770_){
_start:
{
lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = lean_array_get_size(v_keys_2768_);
v___x_2772_ = lean_nat_dec_lt(v_i_2769_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_dec(v_i_2769_);
return v___x_2772_;
}
else
{
lean_object* v_k_x27_2773_; uint8_t v___x_2774_; 
v_k_x27_2773_ = lean_array_fget_borrowed(v_keys_2768_, v_i_2769_);
v___x_2774_ = l_Lean_instBEqExtraModUse_beq(v_k_2770_, v_k_x27_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = lean_unsigned_to_nat(1u);
v___x_2776_ = lean_nat_add(v_i_2769_, v___x_2775_);
lean_dec(v_i_2769_);
v_i_2769_ = v___x_2776_;
goto _start;
}
else
{
lean_dec(v_i_2769_);
return v___x_2774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_2778_, lean_object* v_i_2779_, lean_object* v_k_2780_){
_start:
{
uint8_t v_res_2781_; lean_object* v_r_2782_; 
v_res_2781_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2778_, v_i_2779_, v_k_2780_);
lean_dec_ref(v_k_2780_);
lean_dec_ref(v_keys_2778_);
v_r_2782_ = lean_box(v_res_2781_);
return v_r_2782_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2783_, size_t v_x_2784_, lean_object* v_x_2785_){
_start:
{
if (lean_obj_tag(v_x_2783_) == 0)
{
lean_object* v_es_2786_; lean_object* v___x_2787_; size_t v___x_2788_; size_t v___x_2789_; lean_object* v_j_2790_; lean_object* v___x_2791_; 
v_es_2786_ = lean_ctor_get(v_x_2783_, 0);
v___x_2787_ = lean_box(2);
v___x_2788_ = ((size_t)31ULL);
v___x_2789_ = lean_usize_land(v_x_2784_, v___x_2788_);
v_j_2790_ = lean_usize_to_nat(v___x_2789_);
v___x_2791_ = lean_array_get_borrowed(v___x_2787_, v_es_2786_, v_j_2790_);
lean_dec(v_j_2790_);
switch(lean_obj_tag(v___x_2791_))
{
case 0:
{
lean_object* v_key_2792_; uint8_t v___x_2793_; 
v_key_2792_ = lean_ctor_get(v___x_2791_, 0);
v___x_2793_ = l_Lean_instBEqExtraModUse_beq(v_x_2785_, v_key_2792_);
return v___x_2793_;
}
case 1:
{
lean_object* v_node_2794_; size_t v___x_2795_; size_t v___x_2796_; 
v_node_2794_ = lean_ctor_get(v___x_2791_, 0);
v___x_2795_ = ((size_t)5ULL);
v___x_2796_ = lean_usize_shift_right(v_x_2784_, v___x_2795_);
v_x_2783_ = v_node_2794_;
v_x_2784_ = v___x_2796_;
goto _start;
}
default: 
{
uint8_t v___x_2798_; 
v___x_2798_ = 0;
return v___x_2798_;
}
}
}
else
{
lean_object* v_ks_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v_ks_2799_ = lean_ctor_get(v_x_2783_, 0);
v___x_2800_ = lean_unsigned_to_nat(0u);
v___x_2801_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_ks_2799_, v___x_2800_, v_x_2785_);
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2802_, lean_object* v_x_2803_, lean_object* v_x_2804_){
_start:
{
size_t v_x_16399__boxed_2805_; uint8_t v_res_2806_; lean_object* v_r_2807_; 
v_x_16399__boxed_2805_ = lean_unbox_usize(v_x_2803_);
lean_dec(v_x_2803_);
v_res_2806_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2802_, v_x_16399__boxed_2805_, v_x_2804_);
lean_dec_ref(v_x_2804_);
lean_dec_ref(v_x_2802_);
v_r_2807_ = lean_box(v_res_2806_);
return v_r_2807_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2808_, lean_object* v_x_2809_){
_start:
{
uint64_t v___x_2810_; size_t v___x_2811_; uint8_t v___x_2812_; 
v___x_2810_ = l_Lean_instHashableExtraModUse_hash(v_x_2809_);
v___x_2811_ = lean_uint64_to_usize(v___x_2810_);
v___x_2812_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2808_, v___x_2811_, v_x_2809_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2813_, lean_object* v_x_2814_){
_start:
{
uint8_t v_res_2815_; lean_object* v_r_2816_; 
v_res_2815_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2813_, v_x_2814_);
lean_dec_ref(v_x_2814_);
lean_dec_ref(v_x_2813_);
v_r_2816_ = lean_box(v_res_2815_);
return v_r_2816_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1));
v___x_2820_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0));
v___x_2821_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2820_, v___x_2819_);
return v___x_2821_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2827_ = l_Lean_stringToMessageData(v___x_2826_);
return v___x_2827_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7));
v___x_2830_ = l_Lean_stringToMessageData(v___x_2829_);
return v___x_2830_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2832_ = l_Lean_stringToMessageData(v___x_2831_);
return v___x_2832_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_cls_2836_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2837_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11));
v___x_2838_ = l_Lean_Name_append(v___x_2837_, v_cls_2836_);
return v___x_2838_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13));
v___x_2841_ = l_Lean_stringToMessageData(v___x_2840_);
return v___x_2841_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___x_2844_ = l_Lean_stringToMessageData(v___x_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2849_, uint8_t v_isMeta_2850_, lean_object* v_hint_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2857_; lean_object* v_env_2858_; uint8_t v_isExporting_2859_; lean_object* v___x_2860_; lean_object* v_env_2861_; lean_object* v___x_2862_; lean_object* v_entry_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v___x_2857_ = lean_st_ref_get(v___y_2855_);
v_env_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc_ref(v_env_2858_);
lean_dec(v___x_2857_);
v_isExporting_2859_ = lean_ctor_get_uint8(v_env_2858_, sizeof(void*)*8);
lean_dec_ref(v_env_2858_);
v___x_2860_ = lean_st_ref_get(v___y_2855_);
v_env_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc_ref(v_env_2861_);
lean_dec(v___x_2860_);
v___x_2862_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_2849_);
v_entry_2863_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2863_, 0, v_mod_2849_);
lean_ctor_set_uint8(v_entry_2863_, sizeof(void*)*1, v_isExporting_2859_);
lean_ctor_set_uint8(v_entry_2863_, sizeof(void*)*1 + 1, v_isMeta_2850_);
v___x_2864_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2865_ = lean_box(1);
v___x_2866_ = lean_box(0);
v___x_2909_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2862_, v___x_2864_, v_env_2861_, v___x_2865_, v___x_2866_);
v___x_2910_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2909_, v_entry_2863_);
lean_dec(v___x_2909_);
if (v___x_2910_ == 0)
{
lean_object* v_options_2911_; uint8_t v_hasTrace_2912_; 
v_options_2911_ = lean_ctor_get(v___y_2854_, 2);
v_hasTrace_2912_ = lean_ctor_get_uint8(v_options_2911_, sizeof(void*)*1);
if (v_hasTrace_2912_ == 0)
{
lean_dec(v_hint_2851_);
lean_dec(v_mod_2849_);
v___y_2868_ = v___y_2853_;
v___y_2869_ = v___y_2855_;
goto v___jp_2867_;
}
else
{
lean_object* v_inheritedTraceOptions_2913_; lean_object* v_cls_2914_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___x_2934_; uint8_t v___x_2935_; 
v_inheritedTraceOptions_2913_ = lean_ctor_get(v___y_2854_, 13);
v_cls_2914_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2934_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_2935_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2913_, v_options_2911_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_dec(v_hint_2851_);
lean_dec(v_mod_2849_);
v___y_2868_ = v___y_2853_;
v___y_2869_ = v___y_2855_;
goto v___jp_2867_;
}
else
{
lean_object* v___x_2936_; lean_object* v___y_2938_; 
v___x_2936_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_2859_ == 0)
{
lean_object* v___x_2945_; 
v___x_2945_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_2938_ = v___x_2945_;
goto v___jp_2937_;
}
else
{
lean_object* v___x_2946_; 
v___x_2946_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_2938_ = v___x_2946_;
goto v___jp_2937_;
}
v___jp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_inc_ref(v___y_2938_);
v___x_2939_ = l_Lean_stringToMessageData(v___y_2938_);
v___x_2940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2936_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_2942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
if (v_isMeta_2850_ == 0)
{
lean_object* v___x_2943_; 
v___x_2943_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_2921_ = v___x_2942_;
v___y_2922_ = v___x_2943_;
goto v___jp_2920_;
}
else
{
lean_object* v___x_2944_; 
v___x_2944_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_2921_ = v___x_2942_;
v___y_2922_ = v___x_2944_;
goto v___jp_2920_;
}
}
}
v___jp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___y_2916_);
lean_ctor_set(v___x_2918_, 1, v___y_2917_);
v___x_2919_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2914_, v___x_2918_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_dec_ref_known(v___x_2919_, 1);
v___y_2868_ = v___y_2853_;
v___y_2869_ = v___y_2855_;
goto v___jp_2867_;
}
else
{
lean_dec_ref_known(v_entry_2863_, 1);
return v___x_2919_;
}
}
v___jp_2920_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
lean_inc_ref(v___y_2922_);
v___x_2923_ = l_Lean_stringToMessageData(v___y_2922_);
v___x_2924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___y_2921_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_2926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = l_Lean_MessageData_ofName(v_mod_2849_);
v___x_2928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = l_Lean_Name_isAnonymous(v_hint_2851_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2930_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_2931_ = l_Lean_MessageData_ofName(v_hint_2851_);
v___x_2932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2930_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___y_2916_ = v___x_2928_;
v___y_2917_ = v___x_2932_;
goto v___jp_2915_;
}
else
{
lean_object* v___x_2933_; 
lean_dec(v_hint_2851_);
v___x_2933_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_2916_ = v___x_2928_;
v___y_2917_ = v___x_2933_;
goto v___jp_2915_;
}
}
}
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
lean_dec_ref_known(v_entry_2863_, 1);
lean_dec(v_hint_2851_);
lean_dec(v_mod_2849_);
v___x_2947_ = lean_box(0);
v___x_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
return v___x_2948_;
}
v___jp_2867_:
{
lean_object* v___x_2870_; lean_object* v_toEnvExtension_2871_; lean_object* v_env_2872_; lean_object* v_nextMacroScope_2873_; lean_object* v_ngen_2874_; lean_object* v_auxDeclNGen_2875_; lean_object* v_traceState_2876_; lean_object* v_messages_2877_; lean_object* v_infoState_2878_; lean_object* v_snapshotTasks_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2907_; 
v___x_2870_ = lean_st_ref_take(v___y_2869_);
v_toEnvExtension_2871_ = lean_ctor_get(v___x_2864_, 0);
v_env_2872_ = lean_ctor_get(v___x_2870_, 0);
v_nextMacroScope_2873_ = lean_ctor_get(v___x_2870_, 1);
v_ngen_2874_ = lean_ctor_get(v___x_2870_, 2);
v_auxDeclNGen_2875_ = lean_ctor_get(v___x_2870_, 3);
v_traceState_2876_ = lean_ctor_get(v___x_2870_, 4);
v_messages_2877_ = lean_ctor_get(v___x_2870_, 6);
v_infoState_2878_ = lean_ctor_get(v___x_2870_, 7);
v_snapshotTasks_2879_ = lean_ctor_get(v___x_2870_, 8);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; 
v_unused_2908_ = lean_ctor_get(v___x_2870_, 5);
lean_dec(v_unused_2908_);
v___x_2881_ = v___x_2870_;
v_isShared_2882_ = v_isSharedCheck_2907_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_snapshotTasks_2879_);
lean_inc(v_infoState_2878_);
lean_inc(v_messages_2877_);
lean_inc(v_traceState_2876_);
lean_inc(v_auxDeclNGen_2875_);
lean_inc(v_ngen_2874_);
lean_inc(v_nextMacroScope_2873_);
lean_inc(v_env_2872_);
lean_dec(v___x_2870_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2907_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v_asyncMode_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
v_asyncMode_2883_ = lean_ctor_get(v_toEnvExtension_2871_, 2);
v___x_2884_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2864_, v_env_2872_, v_entry_2863_, v_asyncMode_2883_, v___x_2866_);
v___x_2885_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 5, v___x_2885_);
lean_ctor_set(v___x_2881_, 0, v___x_2884_);
v___x_2887_ = v___x_2881_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2884_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_nextMacroScope_2873_);
lean_ctor_set(v_reuseFailAlloc_2906_, 2, v_ngen_2874_);
lean_ctor_set(v_reuseFailAlloc_2906_, 3, v_auxDeclNGen_2875_);
lean_ctor_set(v_reuseFailAlloc_2906_, 4, v_traceState_2876_);
lean_ctor_set(v_reuseFailAlloc_2906_, 5, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2906_, 6, v_messages_2877_);
lean_ctor_set(v_reuseFailAlloc_2906_, 7, v_infoState_2878_);
lean_ctor_set(v_reuseFailAlloc_2906_, 8, v_snapshotTasks_2879_);
v___x_2887_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v_mctx_2890_; lean_object* v_zetaDeltaFVarIds_2891_; lean_object* v_postponed_2892_; lean_object* v_diag_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2904_; 
v___x_2888_ = lean_st_ref_set(v___y_2869_, v___x_2887_);
v___x_2889_ = lean_st_ref_take(v___y_2868_);
v_mctx_2890_ = lean_ctor_get(v___x_2889_, 0);
v_zetaDeltaFVarIds_2891_ = lean_ctor_get(v___x_2889_, 2);
v_postponed_2892_ = lean_ctor_get(v___x_2889_, 3);
v_diag_2893_ = lean_ctor_get(v___x_2889_, 4);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; 
v_unused_2905_ = lean_ctor_get(v___x_2889_, 1);
lean_dec(v_unused_2905_);
v___x_2895_ = v___x_2889_;
v_isShared_2896_ = v_isSharedCheck_2904_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_diag_2893_);
lean_inc(v_postponed_2892_);
lean_inc(v_zetaDeltaFVarIds_2891_);
lean_inc(v_mctx_2890_);
lean_dec(v___x_2889_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2904_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2897_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 1, v___x_2897_);
v___x_2899_ = v___x_2895_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_mctx_2890_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_zetaDeltaFVarIds_2891_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_postponed_2892_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_diag_2893_);
v___x_2899_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = lean_st_ref_set(v___y_2868_, v___x_2899_);
v___x_2901_ = lean_box(0);
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
return v___x_2902_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_2949_, lean_object* v_isMeta_2950_, lean_object* v_hint_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
uint8_t v_isMeta_boxed_2957_; lean_object* v_res_2958_; 
v_isMeta_boxed_2957_ = lean_unbox(v_isMeta_2950_);
v_res_2958_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2949_, v_isMeta_boxed_2957_, v_hint_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object* v_a_2959_, lean_object* v_x_2960_){
_start:
{
if (lean_obj_tag(v_x_2960_) == 0)
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_box(0);
return v___x_2961_;
}
else
{
lean_object* v_key_2962_; lean_object* v_value_2963_; lean_object* v_tail_2964_; uint8_t v___x_2965_; 
v_key_2962_ = lean_ctor_get(v_x_2960_, 0);
v_value_2963_ = lean_ctor_get(v_x_2960_, 1);
v_tail_2964_ = lean_ctor_get(v_x_2960_, 2);
v___x_2965_ = lean_name_eq(v_key_2962_, v_a_2959_);
if (v___x_2965_ == 0)
{
v_x_2960_ = v_tail_2964_;
goto _start;
}
else
{
lean_object* v___x_2967_; 
lean_inc(v_value_2963_);
v___x_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2967_, 0, v_value_2963_);
return v___x_2967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_a_2968_, lean_object* v_x_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2968_, v_x_2969_);
lean_dec(v_x_2969_);
lean_dec(v_a_2968_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_buckets_2973_; lean_object* v___x_2974_; uint64_t v___y_2976_; 
v_buckets_2973_ = lean_ctor_get(v_m_2971_, 1);
v___x_2974_ = lean_array_get_size(v_buckets_2973_);
if (lean_obj_tag(v_a_2972_) == 0)
{
uint64_t v___x_2990_; 
v___x_2990_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_2976_ = v___x_2990_;
goto v___jp_2975_;
}
else
{
uint64_t v_hash_2991_; 
v_hash_2991_ = lean_ctor_get_uint64(v_a_2972_, sizeof(void*)*2);
v___y_2976_ = v_hash_2991_;
goto v___jp_2975_;
}
v___jp_2975_:
{
uint64_t v___x_2977_; uint64_t v___x_2978_; uint64_t v_fold_2979_; uint64_t v___x_2980_; uint64_t v___x_2981_; uint64_t v___x_2982_; size_t v___x_2983_; size_t v___x_2984_; size_t v___x_2985_; size_t v___x_2986_; size_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2977_ = 32ULL;
v___x_2978_ = lean_uint64_shift_right(v___y_2976_, v___x_2977_);
v_fold_2979_ = lean_uint64_xor(v___y_2976_, v___x_2978_);
v___x_2980_ = 16ULL;
v___x_2981_ = lean_uint64_shift_right(v_fold_2979_, v___x_2980_);
v___x_2982_ = lean_uint64_xor(v_fold_2979_, v___x_2981_);
v___x_2983_ = lean_uint64_to_usize(v___x_2982_);
v___x_2984_ = lean_usize_of_nat(v___x_2974_);
v___x_2985_ = ((size_t)1ULL);
v___x_2986_ = lean_usize_sub(v___x_2984_, v___x_2985_);
v___x_2987_ = lean_usize_land(v___x_2983_, v___x_2986_);
v___x_2988_ = lean_array_uget_borrowed(v_buckets_2973_, v___x_2987_);
v___x_2989_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2972_, v___x_2988_);
return v___x_2989_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_2992_, v_a_2993_);
lean_dec(v_a_2993_);
lean_dec_ref(v_m_2992_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_2995_, lean_object* v_declName_2996_, lean_object* v_as_2997_, size_t v_sz_2998_, size_t v_i_2999_, lean_object* v_b_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
uint8_t v___x_3006_; 
v___x_3006_ = lean_usize_dec_lt(v_i_2999_, v_sz_2998_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; 
lean_dec(v_declName_2996_);
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_b_3000_);
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; lean_object* v_modules_3009_; lean_object* v___x_3010_; lean_object* v_a_3011_; lean_object* v___x_3012_; lean_object* v_toImport_3013_; lean_object* v_module_3014_; uint8_t v___x_3015_; lean_object* v___x_3016_; 
v___x_3008_ = l_Lean_Environment_header(v___x_2995_);
v_modules_3009_ = lean_ctor_get(v___x_3008_, 3);
lean_inc_ref(v_modules_3009_);
lean_dec_ref(v___x_3008_);
v___x_3010_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3011_ = lean_array_uget_borrowed(v_as_2997_, v_i_2999_);
v___x_3012_ = lean_array_get(v___x_3010_, v_modules_3009_, v_a_3011_);
lean_dec_ref(v_modules_3009_);
v_toImport_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc_ref(v_toImport_3013_);
lean_dec(v___x_3012_);
v_module_3014_ = lean_ctor_get(v_toImport_3013_, 0);
lean_inc(v_module_3014_);
lean_dec_ref(v_toImport_3013_);
v___x_3015_ = 0;
lean_inc(v_declName_2996_);
v___x_3016_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3014_, v___x_3015_, v_declName_2996_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v___x_3017_; size_t v___x_3018_; size_t v___x_3019_; 
lean_dec_ref_known(v___x_3016_, 1);
v___x_3017_ = lean_box(0);
v___x_3018_ = ((size_t)1ULL);
v___x_3019_ = lean_usize_add(v_i_2999_, v___x_3018_);
v_i_2999_ = v___x_3019_;
v_b_3000_ = v___x_3017_;
goto _start;
}
else
{
lean_dec(v_declName_2996_);
return v___x_3016_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_3021_, lean_object* v_declName_3022_, lean_object* v_as_3023_, lean_object* v_sz_3024_, lean_object* v_i_3025_, lean_object* v_b_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
size_t v_sz_boxed_3032_; size_t v_i_boxed_3033_; lean_object* v_res_3034_; 
v_sz_boxed_3032_ = lean_unbox_usize(v_sz_3024_);
lean_dec(v_sz_3024_);
v_i_boxed_3033_ = lean_unbox_usize(v_i_3025_);
lean_dec(v_i_3025_);
v_res_3034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_3021_, v_declName_3022_, v_as_3023_, v_sz_boxed_3032_, v_i_boxed_3033_, v_b_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec_ref(v_as_3023_);
lean_dec_ref(v___x_3021_);
return v_res_3034_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3037_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___x_3038_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0));
v___x_3039_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3038_, v___x_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_3042_, uint8_t v_isMeta_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___x_3049_; lean_object* v_env_3053_; lean_object* v___y_3055_; lean_object* v___x_3068_; 
v___x_3049_ = lean_st_ref_get(v___y_3047_);
v_env_3053_ = lean_ctor_get(v___x_3049_, 0);
lean_inc_ref(v_env_3053_);
lean_dec(v___x_3049_);
v___x_3068_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3053_, v_declName_3042_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_dec_ref(v_env_3053_);
lean_dec(v_declName_3042_);
goto v___jp_3050_;
}
else
{
lean_object* v_val_3069_; lean_object* v___x_3070_; lean_object* v_modules_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v_val_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_val_3069_);
lean_dec_ref_known(v___x_3068_, 1);
v___x_3070_ = l_Lean_Environment_header(v_env_3053_);
v_modules_3071_ = lean_ctor_get(v___x_3070_, 3);
lean_inc_ref(v_modules_3071_);
lean_dec_ref(v___x_3070_);
v___x_3072_ = lean_array_get_size(v_modules_3071_);
v___x_3073_ = lean_nat_dec_lt(v_val_3069_, v___x_3072_);
if (v___x_3073_ == 0)
{
lean_dec_ref(v_modules_3071_);
lean_dec(v_val_3069_);
lean_dec_ref(v_env_3053_);
lean_dec(v_declName_3042_);
goto v___jp_3050_;
}
else
{
lean_object* v___x_3074_; lean_object* v_env_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___y_3079_; 
v___x_3074_ = lean_st_ref_get(v___y_3047_);
v_env_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc_ref(v_env_3075_);
lean_dec(v___x_3074_);
v___x_3076_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3077_ = lean_array_fget(v_modules_3071_, v_val_3069_);
lean_dec(v_val_3069_);
lean_dec_ref(v_modules_3071_);
if (v_isMeta_3043_ == 0)
{
lean_dec_ref(v_env_3075_);
v___y_3079_ = v_isMeta_3043_;
goto v___jp_3078_;
}
else
{
uint8_t v___x_3090_; 
lean_inc(v_declName_3042_);
v___x_3090_ = l_Lean_isMarkedMeta(v_env_3075_, v_declName_3042_);
if (v___x_3090_ == 0)
{
v___y_3079_ = v_isMeta_3043_;
goto v___jp_3078_;
}
else
{
uint8_t v___x_3091_; 
v___x_3091_ = 0;
v___y_3079_ = v___x_3091_;
goto v___jp_3078_;
}
}
v___jp_3078_:
{
lean_object* v_toImport_3080_; lean_object* v_module_3081_; lean_object* v___x_3082_; 
v_toImport_3080_ = lean_ctor_get(v___x_3077_, 0);
lean_inc_ref(v_toImport_3080_);
lean_dec(v___x_3077_);
v_module_3081_ = lean_ctor_get(v_toImport_3080_, 0);
lean_inc(v_module_3081_);
lean_dec_ref(v_toImport_3080_);
lean_inc(v_declName_3042_);
v___x_3082_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3081_, v___y_3079_, v_declName_3042_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_dec_ref_known(v___x_3082_, 1);
v___x_3083_ = l_Lean_indirectModUseExt;
v___x_3084_ = lean_box(1);
v___x_3085_ = lean_box(0);
lean_inc_ref(v_env_3053_);
v___x_3086_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3076_, v___x_3083_, v_env_3053_, v___x_3084_, v___x_3085_);
v___x_3087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3086_, v_declName_3042_);
lean_dec(v___x_3086_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3088_; 
v___x_3088_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3055_ = v___x_3088_;
goto v___jp_3054_;
}
else
{
lean_object* v_val_3089_; 
v_val_3089_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_val_3089_);
lean_dec_ref_known(v___x_3087_, 1);
v___y_3055_ = v_val_3089_;
goto v___jp_3054_;
}
}
else
{
lean_dec_ref(v_env_3053_);
lean_dec(v_declName_3042_);
return v___x_3082_;
}
}
}
}
v___jp_3050_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = lean_box(0);
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
return v___x_3052_;
}
v___jp_3054_:
{
lean_object* v___x_3056_; size_t v_sz_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3056_ = lean_box(0);
v_sz_3057_ = lean_array_size(v___y_3055_);
v___x_3058_ = ((size_t)0ULL);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_3053_, v_declName_3042_, v___y_3055_, v_sz_3057_, v___x_3058_, v___x_3056_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec_ref(v___y_3055_);
lean_dec_ref(v_env_3053_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; 
v_unused_3067_ = lean_ctor_get(v___x_3059_, 0);
lean_dec(v_unused_3067_);
v___x_3061_ = v___x_3059_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_dec(v___x_3059_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3056_);
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3056_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
else
{
return v___x_3059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3092_, lean_object* v_isMeta_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
uint8_t v_isMeta_boxed_3099_; lean_object* v_res_3100_; 
v_isMeta_boxed_3099_ = lean_unbox(v_isMeta_3093_);
v_res_3100_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3092_, v_isMeta_boxed_3099_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3101_, uint8_t v_isExporting_3102_, lean_object* v___x_3103_, lean_object* v___y_3104_, lean_object* v___x_3105_, lean_object* v_a_x3f_3106_){
_start:
{
lean_object* v___x_3108_; lean_object* v_env_3109_; lean_object* v_nextMacroScope_3110_; lean_object* v_ngen_3111_; lean_object* v_auxDeclNGen_3112_; lean_object* v_traceState_3113_; lean_object* v_messages_3114_; lean_object* v_infoState_3115_; lean_object* v_snapshotTasks_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3141_; 
v___x_3108_ = lean_st_ref_take(v___y_3101_);
v_env_3109_ = lean_ctor_get(v___x_3108_, 0);
v_nextMacroScope_3110_ = lean_ctor_get(v___x_3108_, 1);
v_ngen_3111_ = lean_ctor_get(v___x_3108_, 2);
v_auxDeclNGen_3112_ = lean_ctor_get(v___x_3108_, 3);
v_traceState_3113_ = lean_ctor_get(v___x_3108_, 4);
v_messages_3114_ = lean_ctor_get(v___x_3108_, 6);
v_infoState_3115_ = lean_ctor_get(v___x_3108_, 7);
v_snapshotTasks_3116_ = lean_ctor_get(v___x_3108_, 8);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; 
v_unused_3142_ = lean_ctor_get(v___x_3108_, 5);
lean_dec(v_unused_3142_);
v___x_3118_ = v___x_3108_;
v_isShared_3119_ = v_isSharedCheck_3141_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_snapshotTasks_3116_);
lean_inc(v_infoState_3115_);
lean_inc(v_messages_3114_);
lean_inc(v_traceState_3113_);
lean_inc(v_auxDeclNGen_3112_);
lean_inc(v_ngen_3111_);
lean_inc(v_nextMacroScope_3110_);
lean_inc(v_env_3109_);
lean_dec(v___x_3108_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3141_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3120_ = l_Lean_Environment_setExporting(v_env_3109_, v_isExporting_3102_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 5, v___x_3103_);
lean_ctor_set(v___x_3118_, 0, v___x_3120_);
v___x_3122_ = v___x_3118_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v_nextMacroScope_3110_);
lean_ctor_set(v_reuseFailAlloc_3140_, 2, v_ngen_3111_);
lean_ctor_set(v_reuseFailAlloc_3140_, 3, v_auxDeclNGen_3112_);
lean_ctor_set(v_reuseFailAlloc_3140_, 4, v_traceState_3113_);
lean_ctor_set(v_reuseFailAlloc_3140_, 5, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3140_, 6, v_messages_3114_);
lean_ctor_set(v_reuseFailAlloc_3140_, 7, v_infoState_3115_);
lean_ctor_set(v_reuseFailAlloc_3140_, 8, v_snapshotTasks_3116_);
v___x_3122_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v_mctx_3125_; lean_object* v_zetaDeltaFVarIds_3126_; lean_object* v_postponed_3127_; lean_object* v_diag_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3138_; 
v___x_3123_ = lean_st_ref_set(v___y_3101_, v___x_3122_);
v___x_3124_ = lean_st_ref_take(v___y_3104_);
v_mctx_3125_ = lean_ctor_get(v___x_3124_, 0);
v_zetaDeltaFVarIds_3126_ = lean_ctor_get(v___x_3124_, 2);
v_postponed_3127_ = lean_ctor_get(v___x_3124_, 3);
v_diag_3128_ = lean_ctor_get(v___x_3124_, 4);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; 
v_unused_3139_ = lean_ctor_get(v___x_3124_, 1);
lean_dec(v_unused_3139_);
v___x_3130_ = v___x_3124_;
v_isShared_3131_ = v_isSharedCheck_3138_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_diag_3128_);
lean_inc(v_postponed_3127_);
lean_inc(v_zetaDeltaFVarIds_3126_);
lean_inc(v_mctx_3125_);
lean_dec(v___x_3124_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3138_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 1, v___x_3105_);
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_mctx_3125_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_zetaDeltaFVarIds_3126_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v_postponed_3127_);
lean_ctor_set(v_reuseFailAlloc_3137_, 4, v_diag_3128_);
v___x_3133_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = lean_st_ref_set(v___y_3104_, v___x_3133_);
v___x_3135_ = lean_box(0);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
return v___x_3136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3143_, lean_object* v_isExporting_3144_, lean_object* v___x_3145_, lean_object* v___y_3146_, lean_object* v___x_3147_, lean_object* v_a_x3f_3148_, lean_object* v___y_3149_){
_start:
{
uint8_t v_isExporting_boxed_3150_; lean_object* v_res_3151_; 
v_isExporting_boxed_3150_ = lean_unbox(v_isExporting_3144_);
v_res_3151_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3143_, v_isExporting_boxed_3150_, v___x_3145_, v___y_3146_, v___x_3147_, v_a_x3f_3148_);
lean_dec(v_a_x3f_3148_);
lean_dec(v___y_3146_);
lean_dec(v___y_3143_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3152_, uint8_t v_isExporting_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v___x_3159_; lean_object* v_env_3160_; uint8_t v_isExporting_3161_; lean_object* v___x_3227_; uint8_t v_isModule_3228_; 
v___x_3159_ = lean_st_ref_get(v___y_3157_);
v_env_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc_ref(v_env_3160_);
lean_dec(v___x_3159_);
v_isExporting_3161_ = lean_ctor_get_uint8(v_env_3160_, sizeof(void*)*8);
v___x_3227_ = l_Lean_Environment_header(v_env_3160_);
lean_dec_ref(v_env_3160_);
v_isModule_3228_ = lean_ctor_get_uint8(v___x_3227_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3227_);
if (v_isModule_3228_ == 0)
{
lean_object* v___x_3229_; 
lean_inc(v___y_3157_);
lean_inc_ref(v___y_3156_);
lean_inc(v___y_3155_);
lean_inc_ref(v___y_3154_);
v___x_3229_ = lean_apply_5(v_x_3152_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, lean_box(0));
return v___x_3229_;
}
else
{
if (v_isExporting_3161_ == 0)
{
if (v_isExporting_3153_ == 0)
{
lean_object* v___x_3230_; 
lean_inc(v___y_3157_);
lean_inc_ref(v___y_3156_);
lean_inc(v___y_3155_);
lean_inc_ref(v___y_3154_);
v___x_3230_ = lean_apply_5(v_x_3152_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, lean_box(0));
return v___x_3230_;
}
else
{
goto v___jp_3162_;
}
}
else
{
if (v_isExporting_3153_ == 0)
{
goto v___jp_3162_;
}
else
{
lean_object* v___x_3231_; 
lean_inc(v___y_3157_);
lean_inc_ref(v___y_3156_);
lean_inc(v___y_3155_);
lean_inc_ref(v___y_3154_);
v___x_3231_ = lean_apply_5(v_x_3152_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, lean_box(0));
return v___x_3231_;
}
}
}
v___jp_3162_:
{
lean_object* v___x_3163_; lean_object* v_env_3164_; lean_object* v_nextMacroScope_3165_; lean_object* v_ngen_3166_; lean_object* v_auxDeclNGen_3167_; lean_object* v_traceState_3168_; lean_object* v_messages_3169_; lean_object* v_infoState_3170_; lean_object* v_snapshotTasks_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3225_; 
v___x_3163_ = lean_st_ref_take(v___y_3157_);
v_env_3164_ = lean_ctor_get(v___x_3163_, 0);
v_nextMacroScope_3165_ = lean_ctor_get(v___x_3163_, 1);
v_ngen_3166_ = lean_ctor_get(v___x_3163_, 2);
v_auxDeclNGen_3167_ = lean_ctor_get(v___x_3163_, 3);
v_traceState_3168_ = lean_ctor_get(v___x_3163_, 4);
v_messages_3169_ = lean_ctor_get(v___x_3163_, 6);
v_infoState_3170_ = lean_ctor_get(v___x_3163_, 7);
v_snapshotTasks_3171_ = lean_ctor_get(v___x_3163_, 8);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3225_ == 0)
{
lean_object* v_unused_3226_; 
v_unused_3226_ = lean_ctor_get(v___x_3163_, 5);
lean_dec(v_unused_3226_);
v___x_3173_ = v___x_3163_;
v_isShared_3174_ = v_isSharedCheck_3225_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_snapshotTasks_3171_);
lean_inc(v_infoState_3170_);
lean_inc(v_messages_3169_);
lean_inc(v_traceState_3168_);
lean_inc(v_auxDeclNGen_3167_);
lean_inc(v_ngen_3166_);
lean_inc(v_nextMacroScope_3165_);
lean_inc(v_env_3164_);
lean_dec(v___x_3163_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3225_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3175_ = l_Lean_Environment_setExporting(v_env_3164_, v_isExporting_3153_);
v___x_3176_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 5, v___x_3176_);
lean_ctor_set(v___x_3173_, 0, v___x_3175_);
v___x_3178_ = v___x_3173_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_nextMacroScope_3165_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v_ngen_3166_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_auxDeclNGen_3167_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v_traceState_3168_);
lean_ctor_set(v_reuseFailAlloc_3224_, 5, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3224_, 6, v_messages_3169_);
lean_ctor_set(v_reuseFailAlloc_3224_, 7, v_infoState_3170_);
lean_ctor_set(v_reuseFailAlloc_3224_, 8, v_snapshotTasks_3171_);
v___x_3178_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v_mctx_3181_; lean_object* v_zetaDeltaFVarIds_3182_; lean_object* v_postponed_3183_; lean_object* v_diag_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3222_; 
v___x_3179_ = lean_st_ref_set(v___y_3157_, v___x_3178_);
v___x_3180_ = lean_st_ref_take(v___y_3155_);
v_mctx_3181_ = lean_ctor_get(v___x_3180_, 0);
v_zetaDeltaFVarIds_3182_ = lean_ctor_get(v___x_3180_, 2);
v_postponed_3183_ = lean_ctor_get(v___x_3180_, 3);
v_diag_3184_ = lean_ctor_get(v___x_3180_, 4);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; 
v_unused_3223_ = lean_ctor_get(v___x_3180_, 1);
lean_dec(v_unused_3223_);
v___x_3186_ = v___x_3180_;
v_isShared_3187_ = v_isSharedCheck_3222_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_diag_3184_);
lean_inc(v_postponed_3183_);
lean_inc(v_zetaDeltaFVarIds_3182_);
lean_inc(v_mctx_3181_);
lean_dec(v___x_3180_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3222_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3188_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 1, v___x_3188_);
v___x_3190_ = v___x_3186_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_mctx_3181_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3221_, 2, v_zetaDeltaFVarIds_3182_);
lean_ctor_set(v_reuseFailAlloc_3221_, 3, v_postponed_3183_);
lean_ctor_set(v_reuseFailAlloc_3221_, 4, v_diag_3184_);
v___x_3190_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; lean_object* v_r_3192_; 
v___x_3191_ = lean_st_ref_set(v___y_3155_, v___x_3190_);
lean_inc(v___y_3157_);
lean_inc_ref(v___y_3156_);
lean_inc(v___y_3155_);
lean_inc_ref(v___y_3154_);
v_r_3192_ = lean_apply_5(v_x_3152_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, lean_box(0));
if (lean_obj_tag(v_r_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3209_; 
v_a_3193_ = lean_ctor_get(v_r_3192_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_r_3192_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3195_ = v_r_3192_;
v_isShared_3196_ = v_isSharedCheck_3209_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v_r_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3209_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
lean_inc(v_a_3193_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set_tag(v___x_3195_, 1);
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
v___x_3199_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3157_, v_isExporting_3161_, v___x_3176_, v___y_3155_, v___x_3188_, v___x_3198_);
lean_dec_ref(v___x_3198_);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v___x_3199_, 0);
lean_dec(v_unused_3207_);
v___x_3201_ = v___x_3199_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_dec(v___x_3199_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v_a_3193_);
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3193_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
v_a_3210_ = lean_ctor_get(v_r_3192_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v_r_3192_, 1);
v___x_3211_ = lean_box(0);
v___x_3212_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3157_, v_isExporting_3161_, v___x_3176_, v___y_3155_, v___x_3188_, v___x_3211_);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3219_ == 0)
{
lean_object* v_unused_3220_; 
v_unused_3220_ = lean_ctor_get(v___x_3212_, 0);
lean_dec(v_unused_3220_);
v___x_3214_ = v___x_3212_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_dec(v___x_3212_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
lean_ctor_set_tag(v___x_3214_, 1);
lean_ctor_set(v___x_3214_, 0, v_a_3210_);
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3210_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3232_, lean_object* v_isExporting_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
uint8_t v_isExporting_boxed_3239_; lean_object* v_res_3240_; 
v_isExporting_boxed_3239_ = lean_unbox(v_isExporting_3233_);
v_res_3240_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3232_, v_isExporting_boxed_3239_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3241_, uint8_t v_when_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
if (v_when_3242_ == 0)
{
lean_object* v___x_3248_; 
lean_inc(v___y_3246_);
lean_inc_ref(v___y_3245_);
lean_inc(v___y_3244_);
lean_inc_ref(v___y_3243_);
v___x_3248_ = lean_apply_5(v_x_3241_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, lean_box(0));
return v___x_3248_;
}
else
{
uint8_t v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = 0;
v___x_3250_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3241_, v___x_3249_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
return v___x_3250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3251_, lean_object* v_when_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
uint8_t v_when_boxed_3258_; lean_object* v_res_3259_; 
v_when_boxed_3258_ = lean_unbox(v_when_3252_);
v_res_3259_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3251_, v_when_boxed_3258_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v___x_3260_, lean_object* v_ext_3261_, uint8_t v_showInfo_3262_, uint8_t v_minIndexable_3263_, lean_object* v_attrName_3264_, lean_object* v_declName_3265_, lean_object* v_stx_3266_, uint8_t v_attrKind_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
uint8_t v___x_3271_; uint8_t v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___y_3288_; lean_object* v___x_3298_; 
v___x_3271_ = 0;
v___x_3272_ = 1;
v___x_3273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3274_ = lean_unsigned_to_nat(32u);
v___x_3275_ = lean_mk_empty_array_with_capacity(v___x_3274_);
lean_dec_ref(v___x_3275_);
v___x_3276_ = lean_unsigned_to_nat(0u);
v___x_3277_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_3279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_3280_ = lean_box(0);
lean_inc(v___x_3260_);
v___x_3281_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3281_, 0, v___x_3273_);
lean_ctor_set(v___x_3281_, 1, v___x_3260_);
lean_ctor_set(v___x_3281_, 2, v___x_3278_);
lean_ctor_set(v___x_3281_, 3, v___x_3279_);
lean_ctor_set(v___x_3281_, 4, v___x_3280_);
lean_ctor_set(v___x_3281_, 5, v___x_3276_);
lean_ctor_set(v___x_3281_, 6, v___x_3280_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*7, v___x_3271_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*7 + 1, v___x_3271_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*7 + 2, v___x_3271_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*7 + 3, v___x_3272_);
v___x_3282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3284_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_3285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3282_);
lean_ctor_set(v___x_3285_, 1, v___x_3283_);
lean_ctor_set(v___x_3285_, 2, v___x_3260_);
lean_ctor_set(v___x_3285_, 3, v___x_3277_);
lean_ctor_set(v___x_3285_, 4, v___x_3284_);
v___x_3286_ = lean_st_mk_ref(v___x_3285_);
lean_inc(v_declName_3265_);
v___x_3298_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3265_, v___x_3271_, v___x_3281_, v___x_3286_, v___y_3268_, v___y_3269_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___f_3303_; lean_object* v___x_3304_; 
lean_dec_ref_known(v___x_3298_, 1);
v___x_3299_ = lean_box(v_attrKind_3267_);
v___x_3300_ = lean_box(v_showInfo_3262_);
v___x_3301_ = lean_box(v_minIndexable_3263_);
v___x_3302_ = lean_box(v___x_3271_);
v___f_3303_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3303_, 0, v_stx_3266_);
lean_closure_set(v___f_3303_, 1, v_ext_3261_);
lean_closure_set(v___f_3303_, 2, v_declName_3265_);
lean_closure_set(v___f_3303_, 3, v___x_3299_);
lean_closure_set(v___f_3303_, 4, v___x_3300_);
lean_closure_set(v___f_3303_, 5, v___x_3301_);
lean_closure_set(v___f_3303_, 6, v___x_3302_);
lean_closure_set(v___f_3303_, 7, v_attrName_3264_);
v___x_3304_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3303_, v___x_3272_, v___x_3281_, v___x_3286_, v___y_3268_, v___y_3269_);
lean_dec_ref_known(v___x_3281_, 7);
v___y_3288_ = v___x_3304_;
goto v___jp_3287_;
}
else
{
lean_dec_ref_known(v___x_3281_, 7);
lean_dec(v_stx_3266_);
lean_dec(v_declName_3265_);
lean_dec(v_attrName_3264_);
lean_dec_ref(v_ext_3261_);
v___y_3288_ = v___x_3298_;
goto v___jp_3287_;
}
v___jp_3287_:
{
if (lean_obj_tag(v___y_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3297_; 
v_a_3289_ = lean_ctor_get(v___y_3288_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___y_3288_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3291_ = v___y_3288_;
v_isShared_3292_ = v_isSharedCheck_3297_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___y_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3297_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = lean_st_ref_get(v___x_3286_);
lean_dec(v___x_3286_);
lean_dec(v___x_3293_);
if (v_isShared_3292_ == 0)
{
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3289_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
else
{
lean_dec(v___x_3286_);
return v___y_3288_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v___x_3305_, lean_object* v_ext_3306_, lean_object* v_showInfo_3307_, lean_object* v_minIndexable_3308_, lean_object* v_attrName_3309_, lean_object* v_declName_3310_, lean_object* v_stx_3311_, lean_object* v_attrKind_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
uint8_t v_showInfo_boxed_3316_; uint8_t v_minIndexable_boxed_3317_; uint8_t v_attrKind_boxed_3318_; lean_object* v_res_3319_; 
v_showInfo_boxed_3316_ = lean_unbox(v_showInfo_3307_);
v_minIndexable_boxed_3317_ = lean_unbox(v_minIndexable_3308_);
v_attrKind_boxed_3318_ = lean_unbox(v_attrKind_3312_);
v_res_3319_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v___x_3305_, v_ext_3306_, v_showInfo_boxed_3316_, v_minIndexable_boxed_3317_, v_attrName_3309_, v_declName_3310_, v_stx_3311_, v_attrKind_boxed_3318_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3342_, uint8_t v_minIndexable_3343_, uint8_t v_showInfo_3344_, lean_object* v_ext_3345_, lean_object* v_ref_3346_){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___f_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___f_3353_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3399_; 
v___x_3348_ = lean_box(1);
v___x_3349_ = lean_box(v_showInfo_3344_);
lean_inc_n(v_attrName_3342_, 2);
lean_inc_ref(v_ext_3345_);
v___f_3350_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3350_, 0, v___x_3348_);
lean_closure_set(v___f_3350_, 1, v_ext_3345_);
lean_closure_set(v___f_3350_, 2, v___x_3349_);
lean_closure_set(v___f_3350_, 3, v_attrName_3342_);
v___x_3351_ = lean_box(v_showInfo_3344_);
v___x_3352_ = lean_box(v_minIndexable_3343_);
v___f_3353_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3353_, 0, v___x_3348_);
lean_closure_set(v___f_3353_, 1, v_ext_3345_);
lean_closure_set(v___f_3353_, 2, v___x_3351_);
lean_closure_set(v___f_3353_, 3, v___x_3352_);
lean_closure_set(v___f_3353_, 4, v_attrName_3342_);
if (v_minIndexable_3343_ == 0)
{
if (v_showInfo_3344_ == 0)
{
lean_inc(v_attrName_3342_);
v___y_3399_ = v_attrName_3342_;
goto v___jp_3398_;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3342_);
v___x_3428_ = lean_name_append_after(v_attrName_3342_, v___x_3427_);
v___y_3399_ = v___x_3428_;
goto v___jp_3398_;
}
}
else
{
if (v_showInfo_3344_ == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3342_);
v___x_3430_ = lean_name_append_after(v_attrName_3342_, v___x_3429_);
v___y_3399_ = v___x_3430_;
goto v___jp_3398_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3342_);
v___x_3432_ = lean_name_append_after(v_attrName_3342_, v___x_3431_);
v___y_3399_ = v___x_3432_;
goto v___jp_3398_;
}
}
v___jp_3354_:
{
lean_object* v___x_3357_; uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3358_ = 1;
v___x_3359_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3342_, v___x_3358_);
v___x_3360_ = lean_string_append(v___x_3357_, v___x_3359_);
v___x_3361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3362_ = lean_string_append(v___x_3360_, v___x_3361_);
v___x_3363_ = lean_string_append(v___x_3362_, v___x_3359_);
v___x_3364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3365_ = lean_string_append(v___x_3363_, v___x_3364_);
v___x_3366_ = lean_string_append(v___x_3365_, v___x_3359_);
v___x_3367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3368_ = lean_string_append(v___x_3366_, v___x_3367_);
v___x_3369_ = lean_string_append(v___x_3368_, v___x_3359_);
v___x_3370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3371_ = lean_string_append(v___x_3369_, v___x_3370_);
v___x_3372_ = lean_string_append(v___x_3371_, v___x_3359_);
v___x_3373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3374_ = lean_string_append(v___x_3372_, v___x_3373_);
v___x_3375_ = lean_string_append(v___x_3374_, v___x_3359_);
v___x_3376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3377_ = lean_string_append(v___x_3375_, v___x_3376_);
v___x_3378_ = lean_string_append(v___x_3377_, v___x_3359_);
v___x_3379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3380_ = lean_string_append(v___x_3378_, v___x_3379_);
v___x_3381_ = lean_string_append(v___x_3380_, v___x_3359_);
v___x_3382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3383_ = lean_string_append(v___x_3381_, v___x_3382_);
v___x_3384_ = lean_string_append(v___x_3383_, v___x_3359_);
v___x_3385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3386_ = lean_string_append(v___x_3384_, v___x_3385_);
v___x_3387_ = lean_string_append(v___x_3386_, v___x_3359_);
v___x_3388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3389_ = lean_string_append(v___x_3387_, v___x_3388_);
v___x_3390_ = lean_string_append(v___x_3389_, v___x_3359_);
lean_dec_ref(v___x_3359_);
v___x_3391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3392_ = lean_string_append(v___x_3390_, v___x_3391_);
v___x_3393_ = lean_string_append(v___y_3356_, v___x_3392_);
lean_dec_ref(v___x_3392_);
v___x_3394_ = 1;
v___x_3395_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3395_, 0, v_ref_3346_);
lean_ctor_set(v___x_3395_, 1, v___y_3355_);
lean_ctor_set(v___x_3395_, 2, v___x_3393_);
lean_ctor_set_uint8(v___x_3395_, sizeof(void*)*3, v___x_3394_);
v___x_3396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v___f_3353_);
lean_ctor_set(v___x_3396_, 2, v___f_3350_);
v___x_3397_ = l_Lean_registerBuiltinAttribute(v___x_3396_);
return v___x_3397_;
}
v___jp_3398_:
{
if (v_minIndexable_3343_ == 0)
{
if (v_showInfo_3344_ == 0)
{
lean_object* v___x_3400_; uint8_t v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3401_ = 1;
lean_inc(v_attrName_3342_);
v___x_3402_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3342_, v___x_3401_);
v___x_3403_ = lean_string_append(v___x_3400_, v___x_3402_);
lean_dec_ref(v___x_3402_);
v___x_3404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3405_ = lean_string_append(v___x_3403_, v___x_3404_);
v___y_3355_ = v___y_3399_;
v___y_3356_ = v___x_3405_;
goto v___jp_3354_;
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3342_);
v___x_3407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3342_, v_showInfo_3344_);
v___x_3408_ = lean_string_append(v___x_3406_, v___x_3407_);
v___x_3409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3410_ = lean_string_append(v___x_3408_, v___x_3409_);
v___x_3411_ = lean_string_append(v___x_3410_, v___x_3407_);
lean_dec_ref(v___x_3407_);
v___x_3412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3413_ = lean_string_append(v___x_3411_, v___x_3412_);
v___y_3355_ = v___y_3399_;
v___y_3356_ = v___x_3413_;
goto v___jp_3354_;
}
}
else
{
if (v_showInfo_3344_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3342_);
v___x_3415_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3342_, v_minIndexable_3343_);
v___x_3416_ = lean_string_append(v___x_3414_, v___x_3415_);
lean_dec_ref(v___x_3415_);
v___x_3417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3418_ = lean_string_append(v___x_3416_, v___x_3417_);
v___y_3355_ = v___y_3399_;
v___y_3356_ = v___x_3418_;
goto v___jp_3354_;
}
else
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3342_);
v___x_3420_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3342_, v_showInfo_3344_);
v___x_3421_ = lean_string_append(v___x_3419_, v___x_3420_);
v___x_3422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3423_ = lean_string_append(v___x_3421_, v___x_3422_);
v___x_3424_ = lean_string_append(v___x_3423_, v___x_3420_);
lean_dec_ref(v___x_3420_);
v___x_3425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3426_ = lean_string_append(v___x_3424_, v___x_3425_);
v___y_3355_ = v___y_3399_;
v___y_3356_ = v___x_3426_;
goto v___jp_3354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3433_, lean_object* v_minIndexable_3434_, lean_object* v_showInfo_3435_, lean_object* v_ext_3436_, lean_object* v_ref_3437_, lean_object* v_a_3438_){
_start:
{
uint8_t v_minIndexable_boxed_3439_; uint8_t v_showInfo_boxed_3440_; lean_object* v_res_3441_; 
v_minIndexable_boxed_3439_ = lean_unbox(v_minIndexable_3434_);
v_showInfo_boxed_3440_ = lean_unbox(v_showInfo_3435_);
v_res_3441_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3433_, v_minIndexable_boxed_3439_, v_showInfo_boxed_3440_, v_ext_3436_, v_ref_3437_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3442_, lean_object* v_msg_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3450_, lean_object* v_msg_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3450_, v_msg_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3458_, uint8_t v_attrKind_3459_, uint8_t v_showInfo_3460_, uint8_t v_minIndexable_3461_, lean_object* v_as_3462_, lean_object* v_as_x27_3463_, lean_object* v_b_3464_, lean_object* v_a_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3458_, v_attrKind_3459_, v_showInfo_3460_, v_minIndexable_3461_, v_as_x27_3463_, v_b_3464_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3472_, lean_object* v_attrKind_3473_, lean_object* v_showInfo_3474_, lean_object* v_minIndexable_3475_, lean_object* v_as_3476_, lean_object* v_as_x27_3477_, lean_object* v_b_3478_, lean_object* v_a_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
uint8_t v_attrKind_boxed_3485_; uint8_t v_showInfo_boxed_3486_; uint8_t v_minIndexable_boxed_3487_; lean_object* v_res_3488_; 
v_attrKind_boxed_3485_ = lean_unbox(v_attrKind_3473_);
v_showInfo_boxed_3486_ = lean_unbox(v_showInfo_3474_);
v_minIndexable_boxed_3487_ = lean_unbox(v_minIndexable_3475_);
v_res_3488_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3472_, v_attrKind_boxed_3485_, v_showInfo_boxed_3486_, v_minIndexable_boxed_3487_, v_as_3476_, v_as_x27_3477_, v_b_3478_, v_a_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v_as_x27_3477_);
lean_dec(v_as_3476_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3489_, lean_object* v_x_3490_, uint8_t v_isExporting_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3490_, v_isExporting_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3498_, lean_object* v_x_3499_, lean_object* v_isExporting_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
uint8_t v_isExporting_boxed_3506_; lean_object* v_res_3507_; 
v_isExporting_boxed_3506_ = lean_unbox(v_isExporting_3500_);
v_res_3507_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3498_, v_x_3499_, v_isExporting_boxed_3506_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3508_, lean_object* v_x_3509_, uint8_t v_when_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3509_, v_when_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3517_, lean_object* v_x_3518_, lean_object* v_when_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
uint8_t v_when_boxed_3525_; lean_object* v_res_3526_; 
v_when_boxed_3525_ = lean_unbox(v_when_3519_);
v_res_3526_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3517_, v_x_3518_, v_when_boxed_3525_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3527_, lean_object* v_m_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3528_, v_a_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3531_, lean_object* v_m_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3531_, v_m_3532_, v_a_3533_);
lean_dec(v_a_3533_);
lean_dec_ref(v_m_3532_);
return v_res_3534_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3535_, lean_object* v_x_3536_, lean_object* v_x_3537_){
_start:
{
uint8_t v___x_3538_; 
v___x_3538_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3536_, v_x_3537_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3539_, lean_object* v_x_3540_, lean_object* v_x_3541_){
_start:
{
uint8_t v_res_3542_; lean_object* v_r_3543_; 
v_res_3542_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3539_, v_x_3540_, v_x_3541_);
lean_dec_ref(v_x_3541_);
lean_dec_ref(v_x_3540_);
v_r_3543_ = lean_box(v_res_3542_);
return v_r_3543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3544_, lean_object* v_a_3545_, lean_object* v_x_3546_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3545_, v_x_3546_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3548_, lean_object* v_a_3549_, lean_object* v_x_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(v_00_u03b2_3548_, v_a_3549_, v_x_3550_);
lean_dec(v_x_3550_);
lean_dec(v_a_3549_);
return v_res_3551_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3552_, lean_object* v_x_3553_, size_t v_x_3554_, lean_object* v_x_3555_){
_start:
{
uint8_t v___x_3556_; 
v___x_3556_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3553_, v_x_3554_, v_x_3555_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3557_, lean_object* v_x_3558_, lean_object* v_x_3559_, lean_object* v_x_3560_){
_start:
{
size_t v_x_17652__boxed_3561_; uint8_t v_res_3562_; lean_object* v_r_3563_; 
v_x_17652__boxed_3561_ = lean_unbox_usize(v_x_3559_);
lean_dec(v_x_3559_);
v_res_3562_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3557_, v_x_3558_, v_x_17652__boxed_3561_, v_x_3560_);
lean_dec_ref(v_x_3560_);
lean_dec_ref(v_x_3558_);
v_r_3563_ = lean_box(v_res_3562_);
return v_r_3563_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_3564_, lean_object* v_keys_3565_, lean_object* v_vals_3566_, lean_object* v_heq_3567_, lean_object* v_i_3568_, lean_object* v_k_3569_){
_start:
{
uint8_t v___x_3570_; 
v___x_3570_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_3565_, v_i_3568_, v_k_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3571_, lean_object* v_keys_3572_, lean_object* v_vals_3573_, lean_object* v_heq_3574_, lean_object* v_i_3575_, lean_object* v_k_3576_){
_start:
{
uint8_t v_res_3577_; lean_object* v_r_3578_; 
v_res_3577_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(v_00_u03b2_3571_, v_keys_3572_, v_vals_3573_, v_heq_3574_, v_i_3575_, v_k_3576_);
lean_dec_ref(v_k_3576_);
lean_dec_ref(v_vals_3573_);
lean_dec_ref(v_keys_3572_);
v_r_3578_ = lean_box(v_res_3577_);
return v_r_3578_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3579_ = lean_box(0);
v___x_3580_ = lean_unsigned_to_nat(16u);
v___x_3581_ = lean_mk_array(v___x_3580_, v___x_3579_);
return v___x_3581_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
lean_ctor_set(v___x_3584_, 1, v___x_3582_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3586_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3587_ = lean_st_mk_ref(v___x_3586_);
v___x_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3591_, lean_object* v_msg_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_ref_3596_; lean_object* v___x_3597_; lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3642_; 
v_ref_3596_ = lean_ctor_get(v___y_3593_, 5);
v___x_3597_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3592_, v___y_3593_, v___y_3594_);
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3642_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3642_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v_traceState_3603_; lean_object* v_env_3604_; lean_object* v_nextMacroScope_3605_; lean_object* v_ngen_3606_; lean_object* v_auxDeclNGen_3607_; lean_object* v_cache_3608_; lean_object* v_messages_3609_; lean_object* v_infoState_3610_; lean_object* v_snapshotTasks_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3641_; 
v___x_3602_ = lean_st_ref_take(v___y_3594_);
v_traceState_3603_ = lean_ctor_get(v___x_3602_, 4);
v_env_3604_ = lean_ctor_get(v___x_3602_, 0);
v_nextMacroScope_3605_ = lean_ctor_get(v___x_3602_, 1);
v_ngen_3606_ = lean_ctor_get(v___x_3602_, 2);
v_auxDeclNGen_3607_ = lean_ctor_get(v___x_3602_, 3);
v_cache_3608_ = lean_ctor_get(v___x_3602_, 5);
v_messages_3609_ = lean_ctor_get(v___x_3602_, 6);
v_infoState_3610_ = lean_ctor_get(v___x_3602_, 7);
v_snapshotTasks_3611_ = lean_ctor_get(v___x_3602_, 8);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3613_ = v___x_3602_;
v_isShared_3614_ = v_isSharedCheck_3641_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_snapshotTasks_3611_);
lean_inc(v_infoState_3610_);
lean_inc(v_messages_3609_);
lean_inc(v_cache_3608_);
lean_inc(v_traceState_3603_);
lean_inc(v_auxDeclNGen_3607_);
lean_inc(v_ngen_3606_);
lean_inc(v_nextMacroScope_3605_);
lean_inc(v_env_3604_);
lean_dec(v___x_3602_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3641_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
uint64_t v_tid_3615_; lean_object* v_traces_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3640_; 
v_tid_3615_ = lean_ctor_get_uint64(v_traceState_3603_, sizeof(void*)*1);
v_traces_3616_ = lean_ctor_get(v_traceState_3603_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_traceState_3603_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3618_ = v_traceState_3603_;
v_isShared_3619_ = v_isSharedCheck_3640_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_traces_3616_);
lean_dec(v_traceState_3603_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3640_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3620_; double v___x_3621_; uint8_t v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3620_ = lean_box(0);
v___x_3621_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_3622_ = 0;
v___x_3623_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_3624_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3624_, 0, v_cls_3591_);
lean_ctor_set(v___x_3624_, 1, v___x_3620_);
lean_ctor_set(v___x_3624_, 2, v___x_3623_);
lean_ctor_set_float(v___x_3624_, sizeof(void*)*3, v___x_3621_);
lean_ctor_set_float(v___x_3624_, sizeof(void*)*3 + 8, v___x_3621_);
lean_ctor_set_uint8(v___x_3624_, sizeof(void*)*3 + 16, v___x_3622_);
v___x_3625_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_3626_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3624_);
lean_ctor_set(v___x_3626_, 1, v_a_3598_);
lean_ctor_set(v___x_3626_, 2, v___x_3625_);
lean_inc(v_ref_3596_);
v___x_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3627_, 0, v_ref_3596_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = l_Lean_PersistentArray_push___redArg(v_traces_3616_, v___x_3627_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 0, v___x_3628_);
v___x_3630_ = v___x_3618_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3628_);
lean_ctor_set_uint64(v_reuseFailAlloc_3639_, sizeof(void*)*1, v_tid_3615_);
v___x_3630_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
lean_object* v___x_3632_; 
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 4, v___x_3630_);
v___x_3632_ = v___x_3613_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_env_3604_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v_nextMacroScope_3605_);
lean_ctor_set(v_reuseFailAlloc_3638_, 2, v_ngen_3606_);
lean_ctor_set(v_reuseFailAlloc_3638_, 3, v_auxDeclNGen_3607_);
lean_ctor_set(v_reuseFailAlloc_3638_, 4, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3638_, 5, v_cache_3608_);
lean_ctor_set(v_reuseFailAlloc_3638_, 6, v_messages_3609_);
lean_ctor_set(v_reuseFailAlloc_3638_, 7, v_infoState_3610_);
lean_ctor_set(v_reuseFailAlloc_3638_, 8, v_snapshotTasks_3611_);
v___x_3632_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3636_; 
v___x_3633_ = lean_st_ref_set(v___y_3594_, v___x_3632_);
v___x_3634_ = lean_box(0);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3634_);
v___x_3636_ = v___x_3600_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3634_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3643_, lean_object* v_msg_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3643_, v_msg_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3649_, uint8_t v_isMeta_3650_, lean_object* v_hint_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v___x_3655_; lean_object* v_env_3656_; uint8_t v_isExporting_3657_; lean_object* v___x_3658_; lean_object* v_env_3659_; lean_object* v___x_3660_; lean_object* v_entry_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___y_3666_; lean_object* v___x_3691_; uint8_t v___x_3692_; 
v___x_3655_ = lean_st_ref_get(v___y_3653_);
v_env_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc_ref(v_env_3656_);
lean_dec(v___x_3655_);
v_isExporting_3657_ = lean_ctor_get_uint8(v_env_3656_, sizeof(void*)*8);
lean_dec_ref(v_env_3656_);
v___x_3658_ = lean_st_ref_get(v___y_3653_);
v_env_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc_ref(v_env_3659_);
lean_dec(v___x_3658_);
v___x_3660_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_3649_);
v_entry_3661_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3661_, 0, v_mod_3649_);
lean_ctor_set_uint8(v_entry_3661_, sizeof(void*)*1, v_isExporting_3657_);
lean_ctor_set_uint8(v_entry_3661_, sizeof(void*)*1 + 1, v_isMeta_3650_);
v___x_3662_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3663_ = lean_box(1);
v___x_3664_ = lean_box(0);
v___x_3691_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3660_, v___x_3662_, v_env_3659_, v___x_3663_, v___x_3664_);
v___x_3692_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3691_, v_entry_3661_);
lean_dec(v___x_3691_);
if (v___x_3692_ == 0)
{
lean_object* v_options_3693_; uint8_t v_hasTrace_3694_; 
v_options_3693_ = lean_ctor_get(v___y_3652_, 2);
v_hasTrace_3694_ = lean_ctor_get_uint8(v_options_3693_, sizeof(void*)*1);
if (v_hasTrace_3694_ == 0)
{
lean_dec(v_hint_3651_);
lean_dec(v_mod_3649_);
v___y_3666_ = v___y_3653_;
goto v___jp_3665_;
}
else
{
lean_object* v_inheritedTraceOptions_3695_; lean_object* v_cls_3696_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v_inheritedTraceOptions_3695_ = lean_ctor_get(v___y_3652_, 13);
v_cls_3696_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_3716_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_3717_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3695_, v_options_3693_, v___x_3716_);
if (v___x_3717_ == 0)
{
lean_dec(v_hint_3651_);
lean_dec(v_mod_3649_);
v___y_3666_ = v___y_3653_;
goto v___jp_3665_;
}
else
{
lean_object* v___x_3718_; lean_object* v___y_3720_; 
v___x_3718_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_3657_ == 0)
{
lean_object* v___x_3727_; 
v___x_3727_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_3720_ = v___x_3727_;
goto v___jp_3719_;
}
else
{
lean_object* v___x_3728_; 
v___x_3728_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_3720_ = v___x_3728_;
goto v___jp_3719_;
}
v___jp_3719_:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_inc_ref(v___y_3720_);
v___x_3721_ = l_Lean_stringToMessageData(v___y_3720_);
v___x_3722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3718_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_3724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3722_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
if (v_isMeta_3650_ == 0)
{
lean_object* v___x_3725_; 
v___x_3725_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3703_ = v___x_3724_;
v___y_3704_ = v___x_3725_;
goto v___jp_3702_;
}
else
{
lean_object* v___x_3726_; 
v___x_3726_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3703_ = v___x_3724_;
v___y_3704_ = v___x_3726_;
goto v___jp_3702_;
}
}
}
v___jp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___y_3698_);
lean_ctor_set(v___x_3700_, 1, v___y_3699_);
v___x_3701_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3696_, v___x_3700_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_dec_ref_known(v___x_3701_, 1);
v___y_3666_ = v___y_3653_;
goto v___jp_3665_;
}
else
{
lean_dec_ref_known(v_entry_3661_, 1);
return v___x_3701_;
}
}
v___jp_3702_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; 
lean_inc_ref(v___y_3704_);
v___x_3705_ = l_Lean_stringToMessageData(v___y_3704_);
v___x_3706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___y_3703_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3706_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
v___x_3709_ = l_Lean_MessageData_ofName(v_mod_3649_);
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3708_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = l_Lean_Name_isAnonymous(v_hint_3651_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3712_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_3713_ = l_Lean_MessageData_ofName(v_hint_3651_);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___y_3698_ = v___x_3710_;
v___y_3699_ = v___x_3714_;
goto v___jp_3697_;
}
else
{
lean_object* v___x_3715_; 
lean_dec(v_hint_3651_);
v___x_3715_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_3698_ = v___x_3710_;
v___y_3699_ = v___x_3715_;
goto v___jp_3697_;
}
}
}
}
else
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_dec_ref_known(v_entry_3661_, 1);
lean_dec(v_hint_3651_);
lean_dec(v_mod_3649_);
v___x_3729_ = lean_box(0);
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
v___jp_3665_:
{
lean_object* v___x_3667_; lean_object* v_toEnvExtension_3668_; lean_object* v_env_3669_; lean_object* v_nextMacroScope_3670_; lean_object* v_ngen_3671_; lean_object* v_auxDeclNGen_3672_; lean_object* v_traceState_3673_; lean_object* v_messages_3674_; lean_object* v_infoState_3675_; lean_object* v_snapshotTasks_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3689_; 
v___x_3667_ = lean_st_ref_take(v___y_3666_);
v_toEnvExtension_3668_ = lean_ctor_get(v___x_3662_, 0);
v_env_3669_ = lean_ctor_get(v___x_3667_, 0);
v_nextMacroScope_3670_ = lean_ctor_get(v___x_3667_, 1);
v_ngen_3671_ = lean_ctor_get(v___x_3667_, 2);
v_auxDeclNGen_3672_ = lean_ctor_get(v___x_3667_, 3);
v_traceState_3673_ = lean_ctor_get(v___x_3667_, 4);
v_messages_3674_ = lean_ctor_get(v___x_3667_, 6);
v_infoState_3675_ = lean_ctor_get(v___x_3667_, 7);
v_snapshotTasks_3676_ = lean_ctor_get(v___x_3667_, 8);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v___x_3667_, 5);
lean_dec(v_unused_3690_);
v___x_3678_ = v___x_3667_;
v_isShared_3679_ = v_isSharedCheck_3689_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_snapshotTasks_3676_);
lean_inc(v_infoState_3675_);
lean_inc(v_messages_3674_);
lean_inc(v_traceState_3673_);
lean_inc(v_auxDeclNGen_3672_);
lean_inc(v_ngen_3671_);
lean_inc(v_nextMacroScope_3670_);
lean_inc(v_env_3669_);
lean_dec(v___x_3667_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3689_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v_asyncMode_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3684_; 
v_asyncMode_3680_ = lean_ctor_get(v_toEnvExtension_3668_, 2);
v___x_3681_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3662_, v_env_3669_, v_entry_3661_, v_asyncMode_3680_, v___x_3664_);
v___x_3682_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 5, v___x_3682_);
lean_ctor_set(v___x_3678_, 0, v___x_3681_);
v___x_3684_ = v___x_3678_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_nextMacroScope_3670_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_ngen_3671_);
lean_ctor_set(v_reuseFailAlloc_3688_, 3, v_auxDeclNGen_3672_);
lean_ctor_set(v_reuseFailAlloc_3688_, 4, v_traceState_3673_);
lean_ctor_set(v_reuseFailAlloc_3688_, 5, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3688_, 6, v_messages_3674_);
lean_ctor_set(v_reuseFailAlloc_3688_, 7, v_infoState_3675_);
lean_ctor_set(v_reuseFailAlloc_3688_, 8, v_snapshotTasks_3676_);
v___x_3684_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = lean_st_ref_set(v___y_3666_, v___x_3684_);
v___x_3686_ = lean_box(0);
v___x_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
return v___x_3687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3731_, lean_object* v_isMeta_3732_, lean_object* v_hint_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
uint8_t v_isMeta_boxed_3737_; lean_object* v_res_3738_; 
v_isMeta_boxed_3737_ = lean_unbox(v_isMeta_3732_);
v_res_3738_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3731_, v_isMeta_boxed_3737_, v_hint_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3739_, lean_object* v_declName_3740_, lean_object* v_as_3741_, size_t v_sz_3742_, size_t v_i_3743_, lean_object* v_b_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
uint8_t v___x_3748_; 
v___x_3748_ = lean_usize_dec_lt(v_i_3743_, v_sz_3742_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; 
lean_dec(v_declName_3740_);
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v_b_3744_);
return v___x_3749_;
}
else
{
lean_object* v___x_3750_; lean_object* v_modules_3751_; lean_object* v___x_3752_; lean_object* v_a_3753_; lean_object* v___x_3754_; lean_object* v_toImport_3755_; lean_object* v_module_3756_; uint8_t v___x_3757_; lean_object* v___x_3758_; 
v___x_3750_ = l_Lean_Environment_header(v___x_3739_);
v_modules_3751_ = lean_ctor_get(v___x_3750_, 3);
lean_inc_ref(v_modules_3751_);
lean_dec_ref(v___x_3750_);
v___x_3752_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3753_ = lean_array_uget_borrowed(v_as_3741_, v_i_3743_);
v___x_3754_ = lean_array_get(v___x_3752_, v_modules_3751_, v_a_3753_);
lean_dec_ref(v_modules_3751_);
v_toImport_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc_ref(v_toImport_3755_);
lean_dec(v___x_3754_);
v_module_3756_ = lean_ctor_get(v_toImport_3755_, 0);
lean_inc(v_module_3756_);
lean_dec_ref(v_toImport_3755_);
v___x_3757_ = 0;
lean_inc(v_declName_3740_);
v___x_3758_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3756_, v___x_3757_, v_declName_3740_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v___x_3759_; size_t v___x_3760_; size_t v___x_3761_; 
lean_dec_ref_known(v___x_3758_, 1);
v___x_3759_ = lean_box(0);
v___x_3760_ = ((size_t)1ULL);
v___x_3761_ = lean_usize_add(v_i_3743_, v___x_3760_);
v_i_3743_ = v___x_3761_;
v_b_3744_ = v___x_3759_;
goto _start;
}
else
{
lean_dec(v_declName_3740_);
return v___x_3758_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3763_, lean_object* v_declName_3764_, lean_object* v_as_3765_, lean_object* v_sz_3766_, lean_object* v_i_3767_, lean_object* v_b_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
size_t v_sz_boxed_3772_; size_t v_i_boxed_3773_; lean_object* v_res_3774_; 
v_sz_boxed_3772_ = lean_unbox_usize(v_sz_3766_);
lean_dec(v_sz_3766_);
v_i_boxed_3773_ = lean_unbox_usize(v_i_3767_);
lean_dec(v_i_3767_);
v_res_3774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3763_, v_declName_3764_, v_as_3765_, v_sz_boxed_3772_, v_i_boxed_3773_, v_b_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec_ref(v_as_3765_);
lean_dec_ref(v___x_3763_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3775_, uint8_t v_isMeta_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v___x_3780_; lean_object* v_env_3784_; lean_object* v___y_3786_; lean_object* v___x_3799_; 
v___x_3780_ = lean_st_ref_get(v___y_3778_);
v_env_3784_ = lean_ctor_get(v___x_3780_, 0);
lean_inc_ref(v_env_3784_);
lean_dec(v___x_3780_);
v___x_3799_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3784_, v_declName_3775_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_dec_ref(v_env_3784_);
lean_dec(v_declName_3775_);
goto v___jp_3781_;
}
else
{
lean_object* v_val_3800_; lean_object* v___x_3801_; lean_object* v_modules_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v_val_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_val_3800_);
lean_dec_ref_known(v___x_3799_, 1);
v___x_3801_ = l_Lean_Environment_header(v_env_3784_);
v_modules_3802_ = lean_ctor_get(v___x_3801_, 3);
lean_inc_ref(v_modules_3802_);
lean_dec_ref(v___x_3801_);
v___x_3803_ = lean_array_get_size(v_modules_3802_);
v___x_3804_ = lean_nat_dec_lt(v_val_3800_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_dec_ref(v_modules_3802_);
lean_dec(v_val_3800_);
lean_dec_ref(v_env_3784_);
lean_dec(v_declName_3775_);
goto v___jp_3781_;
}
else
{
lean_object* v___x_3805_; lean_object* v_env_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; uint8_t v___y_3810_; 
v___x_3805_ = lean_st_ref_get(v___y_3778_);
v_env_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc_ref(v_env_3806_);
lean_dec(v___x_3805_);
v___x_3807_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3808_ = lean_array_fget(v_modules_3802_, v_val_3800_);
lean_dec(v_val_3800_);
lean_dec_ref(v_modules_3802_);
if (v_isMeta_3776_ == 0)
{
lean_dec_ref(v_env_3806_);
v___y_3810_ = v_isMeta_3776_;
goto v___jp_3809_;
}
else
{
uint8_t v___x_3821_; 
lean_inc(v_declName_3775_);
v___x_3821_ = l_Lean_isMarkedMeta(v_env_3806_, v_declName_3775_);
if (v___x_3821_ == 0)
{
v___y_3810_ = v_isMeta_3776_;
goto v___jp_3809_;
}
else
{
uint8_t v___x_3822_; 
v___x_3822_ = 0;
v___y_3810_ = v___x_3822_;
goto v___jp_3809_;
}
}
v___jp_3809_:
{
lean_object* v_toImport_3811_; lean_object* v_module_3812_; lean_object* v___x_3813_; 
v_toImport_3811_ = lean_ctor_get(v___x_3808_, 0);
lean_inc_ref(v_toImport_3811_);
lean_dec(v___x_3808_);
v_module_3812_ = lean_ctor_get(v_toImport_3811_, 0);
lean_inc(v_module_3812_);
lean_dec_ref(v_toImport_3811_);
lean_inc(v_declName_3775_);
v___x_3813_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3812_, v___y_3810_, v_declName_3775_, v___y_3777_, v___y_3778_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
lean_dec_ref_known(v___x_3813_, 1);
v___x_3814_ = l_Lean_indirectModUseExt;
v___x_3815_ = lean_box(1);
v___x_3816_ = lean_box(0);
lean_inc_ref(v_env_3784_);
v___x_3817_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3807_, v___x_3814_, v_env_3784_, v___x_3815_, v___x_3816_);
v___x_3818_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3817_, v_declName_3775_);
lean_dec(v___x_3817_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v___x_3819_; 
v___x_3819_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3786_ = v___x_3819_;
goto v___jp_3785_;
}
else
{
lean_object* v_val_3820_; 
v_val_3820_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_val_3820_);
lean_dec_ref_known(v___x_3818_, 1);
v___y_3786_ = v_val_3820_;
goto v___jp_3785_;
}
}
else
{
lean_dec_ref(v_env_3784_);
lean_dec(v_declName_3775_);
return v___x_3813_;
}
}
}
}
v___jp_3781_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3782_ = lean_box(0);
v___x_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
return v___x_3783_;
}
v___jp_3785_:
{
lean_object* v___x_3787_; size_t v_sz_3788_; size_t v___x_3789_; lean_object* v___x_3790_; 
v___x_3787_ = lean_box(0);
v_sz_3788_ = lean_array_size(v___y_3786_);
v___x_3789_ = ((size_t)0ULL);
v___x_3790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3784_, v_declName_3775_, v___y_3786_, v_sz_3788_, v___x_3789_, v___x_3787_, v___y_3777_, v___y_3778_);
lean_dec_ref(v___y_3786_);
lean_dec_ref(v_env_3784_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3797_ == 0)
{
lean_object* v_unused_3798_; 
v_unused_3798_ = lean_ctor_get(v___x_3790_, 0);
lean_dec(v_unused_3798_);
v___x_3792_ = v___x_3790_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_dec(v___x_3790_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v___x_3787_);
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3787_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
else
{
return v___x_3790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3823_, lean_object* v_isMeta_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
uint8_t v_isMeta_boxed_3828_; lean_object* v_res_3829_; 
v_isMeta_boxed_3828_ = lean_unbox(v_isMeta_3824_);
v_res_3829_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3823_, v_isMeta_boxed_3828_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3834_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3835_ = lean_st_ref_get(v___x_3834_);
v___x_3836_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3835_, v_attrName_3830_);
lean_dec(v___x_3835_);
if (lean_obj_tag(v___x_3836_) == 1)
{
lean_object* v_val_3837_; lean_object* v_ext_3838_; lean_object* v_name_3839_; uint8_t v___x_3840_; lean_object* v___x_3841_; 
v_val_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_val_3837_);
v_ext_3838_ = lean_ctor_get(v_val_3837_, 1);
lean_inc_ref(v_ext_3838_);
lean_dec(v_val_3837_);
v_name_3839_ = lean_ctor_get(v_ext_3838_, 1);
lean_inc(v_name_3839_);
lean_dec_ref(v_ext_3838_);
v___x_3840_ = 1;
v___x_3841_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3839_, v___x_3840_, v_a_3831_, v_a_3832_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3848_ == 0)
{
lean_object* v_unused_3849_; 
v_unused_3849_ = lean_ctor_get(v___x_3841_, 0);
lean_dec(v_unused_3849_);
v___x_3843_ = v___x_3841_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_dec(v___x_3841_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3836_);
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3836_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref_known(v___x_3836_, 1);
v_a_3850_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3841_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3841_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
else
{
lean_object* v___x_3858_; 
v___x_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3836_);
return v___x_3858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3859_, v_a_3860_, v_a_3861_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_attrName_3859_);
return v_res_3863_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3865_, lean_object* v_x_3866_){
_start:
{
if (lean_obj_tag(v_x_3866_) == 0)
{
return v_x_3865_;
}
else
{
lean_object* v_key_3867_; lean_object* v_value_3868_; lean_object* v_tail_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3895_; 
v_key_3867_ = lean_ctor_get(v_x_3866_, 0);
v_value_3868_ = lean_ctor_get(v_x_3866_, 1);
v_tail_3869_ = lean_ctor_get(v_x_3866_, 2);
v_isSharedCheck_3895_ = !lean_is_exclusive(v_x_3866_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3871_ = v_x_3866_;
v_isShared_3872_ = v_isSharedCheck_3895_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_tail_3869_);
lean_inc(v_value_3868_);
lean_inc(v_key_3867_);
lean_dec(v_x_3866_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3895_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; uint64_t v___y_3875_; 
v___x_3873_ = lean_array_get_size(v_x_3865_);
if (lean_obj_tag(v_key_3867_) == 0)
{
uint64_t v___x_3893_; 
v___x_3893_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3875_ = v___x_3893_;
goto v___jp_3874_;
}
else
{
uint64_t v_hash_3894_; 
v_hash_3894_ = lean_ctor_get_uint64(v_key_3867_, sizeof(void*)*2);
v___y_3875_ = v_hash_3894_;
goto v___jp_3874_;
}
v___jp_3874_:
{
uint64_t v___x_3876_; uint64_t v___x_3877_; uint64_t v_fold_3878_; uint64_t v___x_3879_; uint64_t v___x_3880_; uint64_t v___x_3881_; size_t v___x_3882_; size_t v___x_3883_; size_t v___x_3884_; size_t v___x_3885_; size_t v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3876_ = 32ULL;
v___x_3877_ = lean_uint64_shift_right(v___y_3875_, v___x_3876_);
v_fold_3878_ = lean_uint64_xor(v___y_3875_, v___x_3877_);
v___x_3879_ = 16ULL;
v___x_3880_ = lean_uint64_shift_right(v_fold_3878_, v___x_3879_);
v___x_3881_ = lean_uint64_xor(v_fold_3878_, v___x_3880_);
v___x_3882_ = lean_uint64_to_usize(v___x_3881_);
v___x_3883_ = lean_usize_of_nat(v___x_3873_);
v___x_3884_ = ((size_t)1ULL);
v___x_3885_ = lean_usize_sub(v___x_3883_, v___x_3884_);
v___x_3886_ = lean_usize_land(v___x_3882_, v___x_3885_);
v___x_3887_ = lean_array_uget_borrowed(v_x_3865_, v___x_3886_);
lean_inc(v___x_3887_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 2, v___x_3887_);
v___x_3889_ = v___x_3871_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_key_3867_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_value_3868_);
lean_ctor_set(v_reuseFailAlloc_3892_, 2, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_array_uset(v_x_3865_, v___x_3886_, v___x_3889_);
v_x_3865_ = v___x_3890_;
v_x_3866_ = v_tail_3869_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3896_, lean_object* v_source_3897_, lean_object* v_target_3898_){
_start:
{
lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3899_ = lean_array_get_size(v_source_3897_);
v___x_3900_ = lean_nat_dec_lt(v_i_3896_, v___x_3899_);
if (v___x_3900_ == 0)
{
lean_dec_ref(v_source_3897_);
lean_dec(v_i_3896_);
return v_target_3898_;
}
else
{
lean_object* v_es_3901_; lean_object* v___x_3902_; lean_object* v_source_3903_; lean_object* v_target_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v_es_3901_ = lean_array_fget(v_source_3897_, v_i_3896_);
v___x_3902_ = lean_box(0);
v_source_3903_ = lean_array_fset(v_source_3897_, v_i_3896_, v___x_3902_);
v_target_3904_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3898_, v_es_3901_);
v___x_3905_ = lean_unsigned_to_nat(1u);
v___x_3906_ = lean_nat_add(v_i_3896_, v___x_3905_);
lean_dec(v_i_3896_);
v_i_3896_ = v___x_3906_;
v_source_3897_ = v_source_3903_;
v_target_3898_ = v_target_3904_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_3908_){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v_nbuckets_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3909_ = lean_array_get_size(v_data_3908_);
v___x_3910_ = lean_unsigned_to_nat(2u);
v_nbuckets_3911_ = lean_nat_mul(v___x_3909_, v___x_3910_);
v___x_3912_ = lean_unsigned_to_nat(0u);
v___x_3913_ = lean_box(0);
v___x_3914_ = lean_mk_array(v_nbuckets_3911_, v___x_3913_);
v___x_3915_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_3912_, v_data_3908_, v___x_3914_);
return v___x_3915_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_3916_, lean_object* v_x_3917_){
_start:
{
if (lean_obj_tag(v_x_3917_) == 0)
{
uint8_t v___x_3918_; 
v___x_3918_ = 0;
return v___x_3918_;
}
else
{
lean_object* v_key_3919_; lean_object* v_tail_3920_; uint8_t v___x_3921_; 
v_key_3919_ = lean_ctor_get(v_x_3917_, 0);
v_tail_3920_ = lean_ctor_get(v_x_3917_, 2);
v___x_3921_ = lean_name_eq(v_key_3919_, v_a_3916_);
if (v___x_3921_ == 0)
{
v_x_3917_ = v_tail_3920_;
goto _start;
}
else
{
return v___x_3921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_3923_, lean_object* v_x_3924_){
_start:
{
uint8_t v_res_3925_; lean_object* v_r_3926_; 
v_res_3925_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3923_, v_x_3924_);
lean_dec(v_x_3924_);
lean_dec(v_a_3923_);
v_r_3926_ = lean_box(v_res_3925_);
return v_r_3926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_3927_, lean_object* v_b_3928_, lean_object* v_x_3929_){
_start:
{
if (lean_obj_tag(v_x_3929_) == 0)
{
lean_dec(v_b_3928_);
lean_dec(v_a_3927_);
return v_x_3929_;
}
else
{
lean_object* v_key_3930_; lean_object* v_value_3931_; lean_object* v_tail_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3944_; 
v_key_3930_ = lean_ctor_get(v_x_3929_, 0);
v_value_3931_ = lean_ctor_get(v_x_3929_, 1);
v_tail_3932_ = lean_ctor_get(v_x_3929_, 2);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_x_3929_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3934_ = v_x_3929_;
v_isShared_3935_ = v_isSharedCheck_3944_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_tail_3932_);
lean_inc(v_value_3931_);
lean_inc(v_key_3930_);
lean_dec(v_x_3929_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3944_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
uint8_t v___x_3936_; 
v___x_3936_ = lean_name_eq(v_key_3930_, v_a_3927_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3937_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3927_, v_b_3928_, v_tail_3932_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 2, v___x_3937_);
v___x_3939_ = v___x_3934_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_key_3930_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_value_3931_);
lean_ctor_set(v_reuseFailAlloc_3940_, 2, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
else
{
lean_object* v___x_3942_; 
lean_dec(v_value_3931_);
lean_dec(v_key_3930_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 1, v_b_3928_);
lean_ctor_set(v___x_3934_, 0, v_a_3927_);
v___x_3942_ = v___x_3934_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3927_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_b_3928_);
lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_tail_3932_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_3945_, lean_object* v_a_3946_, lean_object* v_b_3947_){
_start:
{
lean_object* v_size_3948_; lean_object* v_buckets_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3995_; 
v_size_3948_ = lean_ctor_get(v_m_3945_, 0);
v_buckets_3949_ = lean_ctor_get(v_m_3945_, 1);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_m_3945_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3951_ = v_m_3945_;
v_isShared_3952_ = v_isSharedCheck_3995_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_buckets_3949_);
lean_inc(v_size_3948_);
lean_dec(v_m_3945_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3995_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3953_; uint64_t v___y_3955_; 
v___x_3953_ = lean_array_get_size(v_buckets_3949_);
if (lean_obj_tag(v_a_3946_) == 0)
{
uint64_t v___x_3993_; 
v___x_3993_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3955_ = v___x_3993_;
goto v___jp_3954_;
}
else
{
uint64_t v_hash_3994_; 
v_hash_3994_ = lean_ctor_get_uint64(v_a_3946_, sizeof(void*)*2);
v___y_3955_ = v_hash_3994_;
goto v___jp_3954_;
}
v___jp_3954_:
{
uint64_t v___x_3956_; uint64_t v___x_3957_; uint64_t v_fold_3958_; uint64_t v___x_3959_; uint64_t v___x_3960_; uint64_t v___x_3961_; size_t v___x_3962_; size_t v___x_3963_; size_t v___x_3964_; size_t v___x_3965_; size_t v___x_3966_; lean_object* v_bkt_3967_; uint8_t v___x_3968_; 
v___x_3956_ = 32ULL;
v___x_3957_ = lean_uint64_shift_right(v___y_3955_, v___x_3956_);
v_fold_3958_ = lean_uint64_xor(v___y_3955_, v___x_3957_);
v___x_3959_ = 16ULL;
v___x_3960_ = lean_uint64_shift_right(v_fold_3958_, v___x_3959_);
v___x_3961_ = lean_uint64_xor(v_fold_3958_, v___x_3960_);
v___x_3962_ = lean_uint64_to_usize(v___x_3961_);
v___x_3963_ = lean_usize_of_nat(v___x_3953_);
v___x_3964_ = ((size_t)1ULL);
v___x_3965_ = lean_usize_sub(v___x_3963_, v___x_3964_);
v___x_3966_ = lean_usize_land(v___x_3962_, v___x_3965_);
v_bkt_3967_ = lean_array_uget_borrowed(v_buckets_3949_, v___x_3966_);
v___x_3968_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3946_, v_bkt_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; lean_object* v_size_x27_3970_; lean_object* v___x_3971_; lean_object* v_buckets_x27_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___x_3969_ = lean_unsigned_to_nat(1u);
v_size_x27_3970_ = lean_nat_add(v_size_3948_, v___x_3969_);
lean_dec(v_size_3948_);
lean_inc(v_bkt_3967_);
v___x_3971_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3971_, 0, v_a_3946_);
lean_ctor_set(v___x_3971_, 1, v_b_3947_);
lean_ctor_set(v___x_3971_, 2, v_bkt_3967_);
v_buckets_x27_3972_ = lean_array_uset(v_buckets_3949_, v___x_3966_, v___x_3971_);
v___x_3973_ = lean_unsigned_to_nat(4u);
v___x_3974_ = lean_nat_mul(v_size_x27_3970_, v___x_3973_);
v___x_3975_ = lean_unsigned_to_nat(3u);
v___x_3976_ = lean_nat_div(v___x_3974_, v___x_3975_);
lean_dec(v___x_3974_);
v___x_3977_ = lean_array_get_size(v_buckets_x27_3972_);
v___x_3978_ = lean_nat_dec_le(v___x_3976_, v___x_3977_);
lean_dec(v___x_3976_);
if (v___x_3978_ == 0)
{
lean_object* v_val_3979_; lean_object* v___x_3981_; 
v_val_3979_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_3972_);
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 1, v_val_3979_);
lean_ctor_set(v___x_3951_, 0, v_size_x27_3970_);
v___x_3981_ = v___x_3951_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_size_x27_3970_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v_val_3979_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
else
{
lean_object* v___x_3984_; 
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 1, v_buckets_x27_3972_);
lean_ctor_set(v___x_3951_, 0, v_size_x27_3970_);
v___x_3984_ = v___x_3951_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_size_x27_3970_);
lean_ctor_set(v_reuseFailAlloc_3985_, 1, v_buckets_x27_3972_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
else
{
lean_object* v___x_3986_; lean_object* v_buckets_x27_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3991_; 
lean_inc(v_bkt_3967_);
v___x_3986_ = lean_box(0);
v_buckets_x27_3987_ = lean_array_uset(v_buckets_3949_, v___x_3966_, v___x_3986_);
v___x_3988_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3946_, v_b_3947_, v_bkt_3967_);
v___x_3989_ = lean_array_uset(v_buckets_x27_3987_, v___x_3966_, v___x_3988_);
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 1, v___x_3989_);
v___x_3991_ = v___x_3951_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_size_3948_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_3996_, lean_object* v_ref_3997_){
_start:
{
lean_object* v___x_3999_; 
lean_inc(v_ref_3997_);
v___x_3999_ = l_Lean_Meta_Grind_mkExtension(v_ref_3997_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; uint8_t v___x_4001_; uint8_t v___x_4002_; lean_object* v___x_4003_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc_n(v_a_4000_, 2);
lean_dec_ref_known(v___x_3999_, 1);
v___x_4001_ = 0;
v___x_4002_ = 1;
lean_inc(v_ref_3997_);
lean_inc(v_attrName_3996_);
v___x_4003_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3996_, v___x_4001_, v___x_4002_, v_a_4000_, v_ref_3997_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v___x_4004_; 
lean_dec_ref_known(v___x_4003_, 1);
lean_inc(v_ref_3997_);
lean_inc(v_a_4000_);
lean_inc(v_attrName_3996_);
v___x_4004_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3996_, v___x_4001_, v___x_4001_, v_a_4000_, v_ref_3997_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v___x_4005_; 
lean_dec_ref_known(v___x_4004_, 1);
lean_inc(v_ref_3997_);
lean_inc(v_a_4000_);
lean_inc(v_attrName_3996_);
v___x_4005_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3996_, v___x_4002_, v___x_4002_, v_a_4000_, v_ref_3997_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v___x_4006_; 
lean_dec_ref_known(v___x_4005_, 1);
lean_inc(v_a_4000_);
lean_inc(v_attrName_3996_);
v___x_4006_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3996_, v___x_4002_, v___x_4001_, v_a_4000_, v_ref_3997_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4017_; 
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4017_ == 0)
{
lean_object* v_unused_4018_; 
v_unused_4018_ = lean_ctor_get(v___x_4006_, 0);
lean_dec(v_unused_4018_);
v___x_4008_ = v___x_4006_;
v_isShared_4009_ = v_isSharedCheck_4017_;
goto v_resetjp_4007_;
}
else
{
lean_dec(v___x_4006_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4017_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4015_; 
v___x_4010_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4011_ = lean_st_ref_take(v___x_4010_);
lean_inc(v_a_4000_);
v___x_4012_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_4011_, v_attrName_3996_, v_a_4000_);
v___x_4013_ = lean_st_ref_set(v___x_4010_, v___x_4012_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v_a_4000_);
v___x_4015_ = v___x_4008_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4000_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
else
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
lean_dec(v_a_4000_);
lean_dec(v_attrName_3996_);
v_a_4019_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_4006_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4006_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_dec(v_a_4000_);
lean_dec(v_ref_3997_);
lean_dec(v_attrName_3996_);
v_a_4027_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_4005_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4005_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
lean_dec(v_a_4000_);
lean_dec(v_ref_3997_);
lean_dec(v_attrName_3996_);
v_a_4035_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4004_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4004_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_dec(v_a_4000_);
lean_dec(v_ref_3997_);
lean_dec(v_attrName_3996_);
v_a_4043_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4003_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4003_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
else
{
lean_dec(v_ref_3997_);
lean_dec(v_attrName_3996_);
return v___x_3999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_4051_, lean_object* v_ref_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Lean_Meta_Grind_registerAttr(v_attrName_4051_, v_ref_4052_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_4055_, lean_object* v_m_4056_, lean_object* v_a_4057_, lean_object* v_b_4058_){
_start:
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_4056_, v_a_4057_, v_b_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_4060_, lean_object* v_a_4061_, lean_object* v_x_4062_){
_start:
{
uint8_t v___x_4063_; 
v___x_4063_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4061_, v_x_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4064_, lean_object* v_a_4065_, lean_object* v_x_4066_){
_start:
{
uint8_t v_res_4067_; lean_object* v_r_4068_; 
v_res_4067_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_4064_, v_a_4065_, v_x_4066_);
lean_dec(v_x_4066_);
lean_dec(v_a_4065_);
v_r_4068_ = lean_box(v_res_4067_);
return v_r_4068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_4069_, lean_object* v_data_4070_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4072_, lean_object* v_a_4073_, lean_object* v_b_4074_, lean_object* v_x_4075_){
_start:
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4073_, v_b_4074_, v_x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4077_, lean_object* v_i_4078_, lean_object* v_source_4079_, lean_object* v_target_4080_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4078_, v_source_4079_, v_target_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4082_, lean_object* v_x_4083_, lean_object* v_x_4084_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4083_, v_x_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_4093_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4094_ = l_Lean_Meta_Grind_registerAttr(v___x_4092_, v___x_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4109_ = l_Lean_Meta_Grind_registerAttr(v___x_4107_, v___x_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4112_, lean_object* v_a_4113_){
_start:
{
lean_object* v___x_4115_; lean_object* v_env_4116_; lean_object* v___x_4117_; lean_object* v_ext_4118_; lean_object* v_toEnvExtension_4119_; lean_object* v_asyncMode_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v_casesTypes_4123_; uint8_t v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4115_ = lean_st_ref_get(v_a_4113_);
v_env_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc_ref(v_env_4116_);
lean_dec(v___x_4115_);
v___x_4117_ = l_Lean_Meta_Grind_grindExt;
v_ext_4118_ = lean_ctor_get(v___x_4117_, 1);
v_toEnvExtension_4119_ = lean_ctor_get(v_ext_4118_, 0);
v_asyncMode_4120_ = lean_ctor_get(v_toEnvExtension_4119_, 2);
v___x_4121_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4122_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4121_, v___x_4117_, v_env_4116_, v_asyncMode_4120_);
v_casesTypes_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc_ref(v_casesTypes_4123_);
lean_dec(v___x_4122_);
v___x_4124_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4123_, v_declName_4112_);
lean_dec_ref(v_casesTypes_4123_);
v___x_4125_ = lean_box(v___x_4124_);
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4127_, v_a_4128_);
lean_dec(v_a_4128_);
lean_dec(v_declName_4127_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4131_, v_a_4133_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_declName_4136_);
return v_res_4140_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_extensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_extensionMapRef);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_grindExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_grindExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_liaExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_liaExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1 = _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1);
l_Lean_Meta_Grind_registerAttr___auto__1 = _init_l_Lean_Meta_Grind_registerAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_Grind_registerAttr___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
