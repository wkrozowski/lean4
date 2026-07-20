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
lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindHom"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value),LEAN_SCALAR_PTR_LITERAL(14, 226, 234, 13, 148, 139, 225, 180)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindHomPred"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value),LEAN_SCALAR_PTR_LITERAL(1, 153, 163, 64, 153, 27, 218, 140)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindHomo"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(88, 142, 231, 82, 214, 226, 8, 218)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__51 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindHomoPred"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value),LEAN_SCALAR_PTR_LITERAL(205, 178, 67, 251, 213, 77, 25, 210)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__54 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__55 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "priority expected"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__57;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__58 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__59 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__60 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__61 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__61_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__62 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__63 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__63_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__64 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__65 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__65_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__66 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__66_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__67 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__67_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__68 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__68_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__68_value)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__69 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__69_value;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "invalid `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " intro]`, `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "symbol priorities must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "normalizer must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "declaration to unfold must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "homomorphism rules must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "homomorphism predicates must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19;
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
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__57(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
v___x_398_ = l_Lean_stringToMessageData(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
lean_inc(v_stx_426_);
v___x_431_ = l_Lean_Syntax_isOfKind(v_stx_426_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_432_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_433_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_436_, v_a_427_, v_a_428_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = l_Lean_Syntax_getArg(v_stx_426_, v___x_438_);
v___x_440_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__9));
lean_inc(v___x_439_);
v___x_441_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__11));
lean_inc(v___x_439_);
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__13));
lean_inc(v___x_439_);
v___x_445_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__15));
lean_inc(v___x_439_);
v___x_447_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__17));
lean_inc(v___x_439_);
v___x_449_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__19));
lean_inc(v___x_439_);
v___x_451_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__21));
lean_inc(v___x_439_);
v___x_453_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__23));
lean_inc(v___x_439_);
v___x_455_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__25));
lean_inc(v___x_439_);
v___x_457_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__27));
lean_inc(v___x_439_);
v___x_459_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
lean_inc(v___x_439_);
v___x_461_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__31));
lean_inc(v___x_439_);
v___x_463_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__33));
lean_inc(v___x_439_);
v___x_465_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__35));
lean_inc(v___x_439_);
v___x_467_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__37));
lean_inc(v___x_439_);
v___x_469_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__39));
lean_inc(v___x_439_);
v___x_471_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__41));
lean_inc(v___x_439_);
v___x_473_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__43));
lean_inc(v___x_439_);
v___x_475_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__45));
lean_inc(v___x_439_);
v___x_477_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__47));
lean_inc(v___x_439_);
v___x_479_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__49));
lean_inc(v___x_439_);
v___x_481_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__51));
lean_inc(v___x_439_);
v___x_483_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__53));
lean_inc(v___x_439_);
v___x_485_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__55));
lean_inc(v___x_439_);
v___x_487_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec(v___x_439_);
v___x_488_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_489_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_492_, v_a_427_, v_a_428_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v_stx_426_);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = l_Lean_Syntax_getArg(v___x_439_, v___x_494_);
lean_dec(v___x_439_);
v___x_496_ = l_Lean_Syntax_isNatLit_x3f(v___x_495_);
if (lean_obj_tag(v___x_496_) == 1)
{
lean_object* v_val_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_505_; 
lean_dec(v___x_495_);
v_val_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_505_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_val_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 5);
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_val_497_);
v___x_502_ = v_reuseFailAlloc_504_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; 
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v___x_496_);
v___x_506_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__57, &l_Lean_Meta_Grind_getAttrKindCore___closed__57_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__57);
v___x_507_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_495_, v___x_506_, v_a_427_, v_a_428_);
lean_dec(v___x_495_);
return v___x_507_;
}
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_508_ = lean_box(11);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_510_ = lean_box(10);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_512_ = lean_box(11);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_514_ = lean_box(10);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_516_ = lean_box(9);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = l_Lean_Syntax_getArg(v___x_439_, v___x_518_);
lean_inc(v___x_519_);
v___x_520_ = l_Lean_Syntax_matchesNull(v___x_519_, v___x_438_);
if (v___x_520_ == 0)
{
uint8_t v___x_521_; 
lean_inc(v___x_519_);
v___x_521_ = l_Lean_Syntax_matchesNull(v___x_519_, v___x_518_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v___x_519_);
lean_dec(v___x_439_);
v___x_522_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_523_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_526_, v_a_427_, v_a_428_);
return v___x_527_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_528_ = l_Lean_Syntax_getArg(v___x_519_, v___x_438_);
lean_dec(v___x_519_);
v___x_529_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
lean_inc(v___x_528_);
v___x_530_ = l_Lean_Syntax_isOfKind(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_532_ = l_Lean_Syntax_isOfKind(v___x_528_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v___x_439_);
v___x_533_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_534_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_537_, v_a_427_, v_a_428_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_539_ = lean_unsigned_to_nat(2u);
v___x_540_ = l_Lean_Syntax_getArg(v___x_439_, v___x_539_);
lean_dec(v___x_439_);
lean_inc(v___x_540_);
v___x_541_ = l_Lean_Syntax_matchesNull(v___x_540_, v___x_438_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; 
v___x_542_ = l_Lean_Syntax_matchesNull(v___x_540_, v___x_518_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_543_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_544_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_547_, v_a_427_, v_a_428_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v_stx_426_);
v___x_549_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_549_, 0, v___x_541_);
lean_ctor_set_uint8(v___x_549_, 1, v___x_431_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; 
lean_dec(v___x_540_);
lean_dec(v_stx_426_);
v___x_551_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_551_, 0, v___x_530_);
lean_ctor_set_uint8(v___x_551_, 1, v___x_530_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
lean_dec(v___x_528_);
v___x_553_ = lean_unsigned_to_nat(2u);
v___x_554_ = l_Lean_Syntax_getArg(v___x_439_, v___x_553_);
lean_dec(v___x_439_);
lean_inc(v___x_554_);
v___x_555_ = l_Lean_Syntax_matchesNull(v___x_554_, v___x_438_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; 
v___x_556_ = l_Lean_Syntax_matchesNull(v___x_554_, v___x_518_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_557_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_558_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_561_, v_a_427_, v_a_428_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v_stx_426_);
v___x_563_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_563_, 0, v___x_431_);
lean_ctor_set_uint8(v___x_563_, 1, v___x_431_);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___x_554_);
lean_dec(v_stx_426_);
v___x_565_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_565_, 0, v___x_431_);
lean_ctor_set_uint8(v___x_565_, 1, v___x_520_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
lean_dec(v___x_519_);
v___x_567_ = lean_unsigned_to_nat(2u);
v___x_568_ = l_Lean_Syntax_getArg(v___x_439_, v___x_567_);
lean_dec(v___x_439_);
lean_inc(v___x_568_);
v___x_569_ = l_Lean_Syntax_matchesNull(v___x_568_, v___x_438_);
if (v___x_569_ == 0)
{
uint8_t v___x_570_; 
v___x_570_ = l_Lean_Syntax_matchesNull(v___x_568_, v___x_518_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_571_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_572_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_575_, v_a_427_, v_a_428_);
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v_stx_426_);
v___x_577_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_577_, 0, v___x_431_);
lean_ctor_set_uint8(v___x_577_, 1, v___x_431_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v___x_568_);
lean_dec(v_stx_426_);
v___x_579_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_579_, 0, v___x_431_);
lean_ctor_set_uint8(v___x_579_, 1, v___x_473_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_581_ = lean_box(7);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_583_ = lean_box(6);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_585_ = lean_box(4);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_587_ = lean_box(2);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_589_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_589_, 0, v___x_431_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_591_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_591_, 0, v___x_461_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_593_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_593_, 0, v___x_431_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_596_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_598_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__64));
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_600_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_602_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__66));
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_604_ = lean_unsigned_to_nat(3u);
v___x_605_ = l_Lean_Syntax_getArg(v___x_439_, v___x_604_);
lean_dec(v___x_439_);
lean_inc(v___x_605_);
v___x_606_ = l_Lean_Syntax_matchesNull(v___x_605_, v___x_438_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_605_);
v___x_608_ = l_Lean_Syntax_matchesNull(v___x_605_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v___x_605_);
v___x_609_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_610_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_613_, v_a_427_, v_a_428_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_615_ = l_Lean_Syntax_getArg(v___x_605_, v___x_438_);
lean_dec(v___x_605_);
v___x_616_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_617_ = l_Lean_Syntax_isOfKind(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_618_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_619_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_622_, v_a_427_, v_a_428_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v_stx_426_);
v___x_624_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_624_, 0, v___x_431_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v___x_605_);
lean_dec(v_stx_426_);
v___x_627_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_627_, 0, v___x_449_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_630_ = lean_unsigned_to_nat(2u);
v___x_631_ = l_Lean_Syntax_getArg(v___x_439_, v___x_630_);
lean_dec(v___x_439_);
lean_inc(v___x_631_);
v___x_632_ = l_Lean_Syntax_matchesNull(v___x_631_, v___x_438_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_631_);
v___x_634_ = l_Lean_Syntax_matchesNull(v___x_631_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec(v___x_631_);
v___x_635_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_636_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_639_, v_a_427_, v_a_428_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_641_ = l_Lean_Syntax_getArg(v___x_631_, v___x_438_);
lean_dec(v___x_631_);
v___x_642_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_643_ = l_Lean_Syntax_isOfKind(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_644_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_645_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_648_, v_a_427_, v_a_428_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec(v_stx_426_);
v___x_650_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_650_, 0, v___x_431_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec(v___x_631_);
lean_dec(v_stx_426_);
v___x_653_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_653_, 0, v___x_447_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = l_Lean_Syntax_getArg(v___x_439_, v___x_656_);
lean_dec(v___x_439_);
lean_inc(v___x_657_);
v___x_658_ = l_Lean_Syntax_matchesNull(v___x_657_, v___x_438_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
lean_inc(v___x_657_);
v___x_659_ = l_Lean_Syntax_matchesNull(v___x_657_, v___x_656_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v___x_657_);
v___x_660_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_661_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_664_, v_a_427_, v_a_428_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = l_Lean_Syntax_getArg(v___x_657_, v___x_438_);
lean_dec(v___x_657_);
v___x_667_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_668_ = l_Lean_Syntax_isOfKind(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_669_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_670_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_673_, v_a_427_, v_a_428_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v_stx_426_);
v___x_675_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_675_, 0, v___x_431_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec(v___x_657_);
lean_dec(v_stx_426_);
v___x_678_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_678_, 0, v___x_445_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec(v___x_439_);
lean_dec(v_stx_426_);
v___x_681_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__67));
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = l_Lean_Syntax_getArg(v___x_439_, v___x_683_);
lean_dec(v___x_439_);
lean_inc(v___x_684_);
v___x_685_ = l_Lean_Syntax_matchesNull(v___x_684_, v___x_438_);
if (v___x_685_ == 0)
{
uint8_t v___x_686_; 
lean_inc(v___x_684_);
v___x_686_ = l_Lean_Syntax_matchesNull(v___x_684_, v___x_683_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v___x_684_);
v___x_687_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_688_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_691_, v_a_427_, v_a_428_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_693_ = l_Lean_Syntax_getArg(v___x_684_, v___x_438_);
lean_dec(v___x_684_);
v___x_694_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_695_ = l_Lean_Syntax_isOfKind(v___x_693_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_696_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_697_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_700_, v_a_427_, v_a_428_);
return v___x_701_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v_stx_426_);
v___x_702_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_702_, 0, v___x_431_);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec(v___x_684_);
lean_dec(v_stx_426_);
v___x_705_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_705_, 0, v___x_441_);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = l_Lean_Syntax_getArg(v___x_439_, v___x_708_);
lean_dec(v___x_439_);
lean_inc(v___x_709_);
v___x_710_ = l_Lean_Syntax_matchesNull(v___x_709_, v___x_438_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
lean_inc(v___x_709_);
v___x_711_ = l_Lean_Syntax_matchesNull(v___x_709_, v___x_708_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v___x_709_);
v___x_712_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_713_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_716_, v_a_427_, v_a_428_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_718_ = l_Lean_Syntax_getArg(v___x_709_, v___x_438_);
lean_dec(v___x_709_);
v___x_719_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_720_ = l_Lean_Syntax_isOfKind(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_721_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_722_ = l_Lean_MessageData_ofSyntax(v_stx_426_);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_725_, v_a_427_, v_a_428_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec(v_stx_426_);
v___x_727_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_727_, 0, v___x_431_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec(v___x_709_);
lean_dec(v_stx_426_);
v___x_730_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__69));
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_732_, v_a_733_, v_a_734_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_737_, lean_object* v_msg_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_738_, v___y_739_, v___y_740_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_743_, lean_object* v_msg_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_743_, v_msg_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_749_, lean_object* v_ref_750_, lean_object* v_msg_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_750_, v_msg_751_, v___y_752_, v___y_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_756_, lean_object* v_ref_757_, lean_object* v_msg_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_756_, v_ref_757_, v_msg_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v_ref_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = l_Lean_Syntax_getArg(v_stx_763_, v___x_767_);
v___x_769_ = l_Lean_Syntax_isNone(v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = l_Lean_Syntax_getArg(v___x_768_, v___x_770_);
lean_dec(v___x_768_);
v___x_772_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_771_, v_a_764_, v_a_765_);
return v___x_772_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec(v___x_768_);
v___x_773_ = lean_box(3);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_stx_775_);
return v_res_779_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_782_ = l_Lean_stringToMessageData(v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_787_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_786_, v_a_783_, v_a_784_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_793_, v_a_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_797_, v_a_798_, v_a_799_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
return v_res_801_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_802_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_807_, lean_object* v_b_808_, uint8_t v_kind_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_currNamespace_813_; lean_object* v___x_814_; lean_object* v_env_815_; lean_object* v_nextMacroScope_816_; lean_object* v_ngen_817_; lean_object* v_auxDeclNGen_818_; lean_object* v_traceState_819_; lean_object* v_messages_820_; lean_object* v_infoState_821_; lean_object* v_snapshotTasks_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_834_; 
v_currNamespace_813_ = lean_ctor_get(v___y_810_, 6);
v___x_814_ = lean_st_ref_take(v___y_811_);
v_env_815_ = lean_ctor_get(v___x_814_, 0);
v_nextMacroScope_816_ = lean_ctor_get(v___x_814_, 1);
v_ngen_817_ = lean_ctor_get(v___x_814_, 2);
v_auxDeclNGen_818_ = lean_ctor_get(v___x_814_, 3);
v_traceState_819_ = lean_ctor_get(v___x_814_, 4);
v_messages_820_ = lean_ctor_get(v___x_814_, 6);
v_infoState_821_ = lean_ctor_get(v___x_814_, 7);
v_snapshotTasks_822_ = lean_ctor_get(v___x_814_, 8);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v___x_814_, 5);
lean_dec(v_unused_835_);
v___x_824_ = v___x_814_;
v_isShared_825_ = v_isSharedCheck_834_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_snapshotTasks_822_);
lean_inc(v_infoState_821_);
lean_inc(v_messages_820_);
lean_inc(v_traceState_819_);
lean_inc(v_auxDeclNGen_818_);
lean_inc(v_ngen_817_);
lean_inc(v_nextMacroScope_816_);
lean_inc(v_env_815_);
lean_dec(v___x_814_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_834_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
lean_inc(v_currNamespace_813_);
v___x_826_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_815_, v_ext_807_, v_b_808_, v_kind_809_, v_currNamespace_813_);
v___x_827_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 5, v___x_827_);
lean_ctor_set(v___x_824_, 0, v___x_826_);
v___x_829_ = v___x_824_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_nextMacroScope_816_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_ngen_817_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v_auxDeclNGen_818_);
lean_ctor_set(v_reuseFailAlloc_833_, 4, v_traceState_819_);
lean_ctor_set(v_reuseFailAlloc_833_, 5, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_833_, 6, v_messages_820_);
lean_ctor_set(v_reuseFailAlloc_833_, 7, v_infoState_821_);
lean_ctor_set(v_reuseFailAlloc_833_, 8, v_snapshotTasks_822_);
v___x_829_ = v_reuseFailAlloc_833_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = lean_st_ref_set(v___y_811_, v___x_829_);
v___x_831_ = lean_box(0);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_836_, lean_object* v_b_837_, lean_object* v_kind_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
uint8_t v_kind_boxed_842_; lean_object* v_res_843_; 
v_kind_boxed_842_ = lean_unbox(v_kind_838_);
v_res_843_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_836_, v_b_837_, v_kind_boxed_842_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_844_, lean_object* v_00_u03b2_845_, lean_object* v_00_u03c3_846_, lean_object* v_ext_847_, lean_object* v_b_848_, uint8_t v_kind_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_847_, v_b_848_, v_kind_849_, v___y_850_, v___y_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_00_u03c3_856_, lean_object* v_ext_857_, lean_object* v_b_858_, lean_object* v_kind_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
uint8_t v_kind_boxed_863_; lean_object* v_res_864_; 
v_kind_boxed_863_ = lean_unbox(v_kind_859_);
v_res_864_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_854_, v_00_u03b2_855_, v_00_u03c3_856_, v_ext_857_, v_b_858_, v_kind_boxed_863_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_865_, lean_object* v_declName_866_, uint8_t v_eager_867_, uint8_t v_attrKind_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___x_872_; 
lean_inc(v_declName_866_);
v___x_872_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_866_, v_eager_867_, v_a_869_, v_a_870_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec_ref_known(v___x_872_, 1);
v___x_873_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_873_, 0, v_declName_866_);
lean_ctor_set_uint8(v___x_873_, sizeof(void*)*1, v_eager_867_);
v___x_874_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_865_, v___x_873_, v_attrKind_868_, v_a_869_, v_a_870_);
return v___x_874_;
}
else
{
lean_dec(v_declName_866_);
lean_dec_ref(v_ext_865_);
return v___x_872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_875_, lean_object* v_declName_876_, lean_object* v_eager_877_, lean_object* v_attrKind_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
uint8_t v_eager_boxed_882_; uint8_t v_attrKind_boxed_883_; lean_object* v_res_884_; 
v_eager_boxed_882_ = lean_unbox(v_eager_877_);
v_attrKind_boxed_883_ = lean_unbox(v_attrKind_878_);
v_res_884_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_875_, v_declName_876_, v_eager_boxed_882_, v_attrKind_boxed_883_, v_a_879_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_885_, lean_object* v_declName_886_, uint8_t v_attrKind_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_891_; 
lean_inc(v_declName_886_);
v___x_891_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_886_, v_a_888_, v_a_889_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_899_; 
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v___x_891_, 0);
lean_dec(v_unused_900_);
v___x_893_ = v___x_891_;
v_isShared_894_ = v_isSharedCheck_899_;
goto v_resetjp_892_;
}
else
{
lean_dec(v___x_891_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_899_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v_declName_886_);
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_declName_886_);
v___x_896_ = v_reuseFailAlloc_898_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_885_, v___x_896_, v_attrKind_887_, v_a_888_, v_a_889_);
return v___x_897_;
}
}
}
else
{
lean_dec(v_declName_886_);
lean_dec_ref(v_ext_885_);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_901_, lean_object* v_declName_902_, lean_object* v_attrKind_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
uint8_t v_attrKind_boxed_907_; lean_object* v_res_908_; 
v_attrKind_boxed_907_ = lean_unbox(v_attrKind_903_);
v_res_908_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_901_, v_declName_902_, v_attrKind_boxed_907_, v_a_904_, v_a_905_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_909_, lean_object* v_declName_910_, uint8_t v_attrKind_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_915_, 0, v_declName_910_);
v___x_916_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_909_, v___x_915_, v_attrKind_911_, v_a_912_, v_a_913_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_917_, lean_object* v_declName_918_, lean_object* v_attrKind_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
uint8_t v_attrKind_boxed_923_; lean_object* v_res_924_; 
v_attrKind_boxed_923_ = lean_unbox(v_attrKind_919_);
v_res_924_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_917_, v_declName_918_, v_attrKind_boxed_923_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_925_, lean_object* v_s_926_){
_start:
{
lean_object* v_casesTypes_927_; lean_object* v_funCC_928_; lean_object* v_ematch_929_; lean_object* v_inj_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
v_casesTypes_927_ = lean_ctor_get(v_s_926_, 0);
v_funCC_928_ = lean_ctor_get(v_s_926_, 2);
v_ematch_929_ = lean_ctor_get(v_s_926_, 3);
v_inj_930_ = lean_ctor_get(v_s_926_, 4);
v_isSharedCheck_937_ = !lean_is_exclusive(v_s_926_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_s_926_, 1);
lean_dec(v_unused_938_);
v___x_932_ = v_s_926_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_inj_930_);
lean_inc(v_ematch_929_);
lean_inc(v_funCC_928_);
lean_inc(v_casesTypes_927_);
lean_dec(v_s_926_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v_a_925_);
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_casesTypes_927_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_a_925_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_funCC_928_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v_ematch_929_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v_inj_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_939_, lean_object* v_declName_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v___x_944_; lean_object* v_ext_945_; lean_object* v_toEnvExtension_946_; lean_object* v_env_947_; lean_object* v_asyncMode_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_extThms_951_; lean_object* v___x_952_; 
v___x_944_ = lean_st_ref_get(v_a_942_);
v_ext_945_ = lean_ctor_get(v_ext_939_, 1);
v_toEnvExtension_946_ = lean_ctor_get(v_ext_945_, 0);
v_env_947_ = lean_ctor_get(v___x_944_, 0);
lean_inc_ref(v_env_947_);
lean_dec(v___x_944_);
v_asyncMode_948_ = lean_ctor_get(v_toEnvExtension_946_, 2);
v___x_949_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_950_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_949_, v_ext_939_, v_env_947_, v_asyncMode_948_);
v_extThms_951_ = lean_ctor_get(v___x_950_, 1);
lean_inc_ref(v_extThms_951_);
lean_dec(v___x_950_);
v___x_952_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_951_, v_declName_940_, v_a_941_, v_a_942_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_982_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_982_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_982_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_982_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v_env_958_; lean_object* v_nextMacroScope_959_; lean_object* v_ngen_960_; lean_object* v_auxDeclNGen_961_; lean_object* v_traceState_962_; lean_object* v_messages_963_; lean_object* v_infoState_964_; lean_object* v_snapshotTasks_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_980_; 
v___x_957_ = lean_st_ref_take(v_a_942_);
v_env_958_ = lean_ctor_get(v___x_957_, 0);
v_nextMacroScope_959_ = lean_ctor_get(v___x_957_, 1);
v_ngen_960_ = lean_ctor_get(v___x_957_, 2);
v_auxDeclNGen_961_ = lean_ctor_get(v___x_957_, 3);
v_traceState_962_ = lean_ctor_get(v___x_957_, 4);
v_messages_963_ = lean_ctor_get(v___x_957_, 6);
v_infoState_964_ = lean_ctor_get(v___x_957_, 7);
v_snapshotTasks_965_ = lean_ctor_get(v___x_957_, 8);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v___x_957_, 5);
lean_dec(v_unused_981_);
v___x_967_ = v___x_957_;
v_isShared_968_ = v_isSharedCheck_980_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_snapshotTasks_965_);
lean_inc(v_infoState_964_);
lean_inc(v_messages_963_);
lean_inc(v_traceState_962_);
lean_inc(v_auxDeclNGen_961_);
lean_inc(v_ngen_960_);
lean_inc(v_nextMacroScope_959_);
lean_inc(v_env_958_);
lean_dec(v___x_957_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_980_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___f_969_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_969_, 0, v_a_953_);
v___x_970_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_939_, v_env_958_, v___f_969_);
v___x_971_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 5, v___x_971_);
lean_ctor_set(v___x_967_, 0, v___x_970_);
v___x_973_ = v___x_967_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_nextMacroScope_959_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_ngen_960_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_auxDeclNGen_961_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_traceState_962_);
lean_ctor_set(v_reuseFailAlloc_979_, 5, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_979_, 6, v_messages_963_);
lean_ctor_set(v_reuseFailAlloc_979_, 7, v_infoState_964_);
lean_ctor_set(v_reuseFailAlloc_979_, 8, v_snapshotTasks_965_);
v___x_973_ = v_reuseFailAlloc_979_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_974_ = lean_st_ref_set(v_a_942_, v___x_973_);
v___x_975_ = lean_box(0);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_975_);
v___x_977_ = v___x_955_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec_ref(v_ext_939_);
v_a_983_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_952_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_952_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_991_, lean_object* v_declName_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_991_, v_declName_992_, v_a_993_, v_a_994_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_997_, lean_object* v_s_998_){
_start:
{
lean_object* v_extThms_999_; lean_object* v_funCC_1000_; lean_object* v_ematch_1001_; lean_object* v_inj_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_extThms_999_ = lean_ctor_get(v_s_998_, 1);
v_funCC_1000_ = lean_ctor_get(v_s_998_, 2);
v_ematch_1001_ = lean_ctor_get(v_s_998_, 3);
v_inj_1002_ = lean_ctor_get(v_s_998_, 4);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_s_998_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_s_998_, 0);
lean_dec(v_unused_1010_);
v___x_1004_ = v_s_998_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_inj_1002_);
lean_inc(v_ematch_1001_);
lean_inc(v_funCC_1000_);
lean_inc(v_extThms_999_);
lean_dec(v_s_998_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_a_997_);
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_997_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_extThms_999_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_funCC_1000_);
lean_ctor_set(v_reuseFailAlloc_1008_, 3, v_ematch_1001_);
lean_ctor_set(v_reuseFailAlloc_1008_, 4, v_inj_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_1011_, lean_object* v_declName_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; 
lean_inc(v_declName_1012_);
v___x_1016_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_1012_, v_a_1013_, v_a_1014_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v___x_1017_; lean_object* v_ext_1018_; lean_object* v_toEnvExtension_1019_; lean_object* v_env_1020_; lean_object* v_asyncMode_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_casesTypes_1024_; lean_object* v___x_1025_; 
lean_dec_ref_known(v___x_1016_, 1);
v___x_1017_ = lean_st_ref_get(v_a_1014_);
v_ext_1018_ = lean_ctor_get(v_ext_1011_, 1);
v_toEnvExtension_1019_ = lean_ctor_get(v_ext_1018_, 0);
v_env_1020_ = lean_ctor_get(v___x_1017_, 0);
lean_inc_ref(v_env_1020_);
lean_dec(v___x_1017_);
v_asyncMode_1021_ = lean_ctor_get(v_toEnvExtension_1019_, 2);
v___x_1022_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1023_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1022_, v_ext_1011_, v_env_1020_, v_asyncMode_1021_);
v_casesTypes_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc_ref(v_casesTypes_1024_);
lean_dec(v___x_1023_);
v___x_1025_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_1024_, v_declName_1012_, v_a_1013_, v_a_1014_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1055_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1055_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1055_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v_env_1031_; lean_object* v_nextMacroScope_1032_; lean_object* v_ngen_1033_; lean_object* v_auxDeclNGen_1034_; lean_object* v_traceState_1035_; lean_object* v_messages_1036_; lean_object* v_infoState_1037_; lean_object* v_snapshotTasks_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1053_; 
v___x_1030_ = lean_st_ref_take(v_a_1014_);
v_env_1031_ = lean_ctor_get(v___x_1030_, 0);
v_nextMacroScope_1032_ = lean_ctor_get(v___x_1030_, 1);
v_ngen_1033_ = lean_ctor_get(v___x_1030_, 2);
v_auxDeclNGen_1034_ = lean_ctor_get(v___x_1030_, 3);
v_traceState_1035_ = lean_ctor_get(v___x_1030_, 4);
v_messages_1036_ = lean_ctor_get(v___x_1030_, 6);
v_infoState_1037_ = lean_ctor_get(v___x_1030_, 7);
v_snapshotTasks_1038_ = lean_ctor_get(v___x_1030_, 8);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v___x_1030_, 5);
lean_dec(v_unused_1054_);
v___x_1040_ = v___x_1030_;
v_isShared_1041_ = v_isSharedCheck_1053_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snapshotTasks_1038_);
lean_inc(v_infoState_1037_);
lean_inc(v_messages_1036_);
lean_inc(v_traceState_1035_);
lean_inc(v_auxDeclNGen_1034_);
lean_inc(v_ngen_1033_);
lean_inc(v_nextMacroScope_1032_);
lean_inc(v_env_1031_);
lean_dec(v___x_1030_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1053_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___f_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___f_1042_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_1042_, 0, v_a_1026_);
v___x_1043_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1011_, v_env_1031_, v___f_1042_);
v___x_1044_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 5, v___x_1044_);
lean_ctor_set(v___x_1040_, 0, v___x_1043_);
v___x_1046_ = v___x_1040_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_nextMacroScope_1032_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_ngen_1033_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v_auxDeclNGen_1034_);
lean_ctor_set(v_reuseFailAlloc_1052_, 4, v_traceState_1035_);
lean_ctor_set(v_reuseFailAlloc_1052_, 5, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1052_, 6, v_messages_1036_);
lean_ctor_set(v_reuseFailAlloc_1052_, 7, v_infoState_1037_);
lean_ctor_set(v_reuseFailAlloc_1052_, 8, v_snapshotTasks_1038_);
v___x_1046_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1047_ = lean_st_ref_set(v_a_1014_, v___x_1046_);
v___x_1048_ = lean_box(0);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1048_);
v___x_1050_ = v___x_1028_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v_ext_1011_);
v_a_1056_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1025_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1025_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_dec(v_declName_1012_);
lean_dec_ref(v_ext_1011_);
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_1064_, lean_object* v_declName_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1064_, v_declName_1065_, v_a_1066_, v_a_1067_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_1070_, lean_object* v_s_1071_){
_start:
{
lean_object* v_casesTypes_1072_; lean_object* v_extThms_1073_; lean_object* v_ematch_1074_; lean_object* v_inj_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_casesTypes_1072_ = lean_ctor_get(v_s_1071_, 0);
v_extThms_1073_ = lean_ctor_get(v_s_1071_, 1);
v_ematch_1074_ = lean_ctor_get(v_s_1071_, 3);
v_inj_1075_ = lean_ctor_get(v_s_1071_, 4);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_s_1071_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v_s_1071_, 2);
lean_dec(v_unused_1083_);
v___x_1077_ = v_s_1071_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_inj_1075_);
lean_inc(v_ematch_1074_);
lean_inc(v_extThms_1073_);
lean_inc(v_casesTypes_1072_);
lean_dec(v_s_1071_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 2, v___x_1070_);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_casesTypes_1072_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_extThms_1073_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v_ematch_1074_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v_inj_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_1084_, lean_object* v_t_1085_){
_start:
{
if (lean_obj_tag(v_t_1085_) == 0)
{
lean_object* v_k_1086_; lean_object* v_v_1087_; lean_object* v_l_1088_; lean_object* v_r_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1743_; 
v_k_1086_ = lean_ctor_get(v_t_1085_, 1);
v_v_1087_ = lean_ctor_get(v_t_1085_, 2);
v_l_1088_ = lean_ctor_get(v_t_1085_, 3);
v_r_1089_ = lean_ctor_get(v_t_1085_, 4);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_t_1085_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; 
v_unused_1744_ = lean_ctor_get(v_t_1085_, 0);
lean_dec(v_unused_1744_);
v___x_1091_ = v_t_1085_;
v_isShared_1092_ = v_isSharedCheck_1743_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_r_1089_);
lean_inc(v_l_1088_);
lean_inc(v_v_1087_);
lean_inc(v_k_1086_);
lean_dec(v_t_1085_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1743_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
uint8_t v___x_1093_; 
v___x_1093_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1084_, v_k_1086_);
switch(v___x_1093_)
{
case 0:
{
lean_object* v_impl_1094_; lean_object* v___x_1095_; 
v_impl_1094_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1084_, v_l_1088_);
v___x_1095_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1094_) == 0)
{
if (lean_obj_tag(v_r_1089_) == 0)
{
lean_object* v_size_1096_; lean_object* v_size_1097_; lean_object* v_k_1098_; lean_object* v_v_1099_; lean_object* v_l_1100_; lean_object* v_r_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_size_1096_ = lean_ctor_get(v_impl_1094_, 0);
lean_inc(v_size_1096_);
v_size_1097_ = lean_ctor_get(v_r_1089_, 0);
v_k_1098_ = lean_ctor_get(v_r_1089_, 1);
v_v_1099_ = lean_ctor_get(v_r_1089_, 2);
v_l_1100_ = lean_ctor_get(v_r_1089_, 3);
lean_inc(v_l_1100_);
v_r_1101_ = lean_ctor_get(v_r_1089_, 4);
v___x_1102_ = lean_unsigned_to_nat(3u);
v___x_1103_ = lean_nat_mul(v___x_1102_, v_size_1096_);
v___x_1104_ = lean_nat_dec_lt(v___x_1103_, v_size_1097_);
lean_dec(v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_dec(v_l_1100_);
v___x_1105_ = lean_nat_add(v___x_1095_, v_size_1096_);
lean_dec(v_size_1096_);
v___x_1106_ = lean_nat_add(v___x_1105_, v_size_1097_);
lean_dec(v___x_1105_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 3, v_impl_1094_);
lean_ctor_set(v___x_1091_, 0, v___x_1106_);
v___x_1108_ = v___x_1091_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v_impl_1094_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_r_1089_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
else
{
lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1173_; 
lean_inc(v_r_1101_);
lean_inc(v_v_1099_);
lean_inc(v_k_1098_);
lean_inc(v_size_1097_);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_r_1089_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; lean_object* v_unused_1177_; lean_object* v_unused_1178_; 
v_unused_1174_ = lean_ctor_get(v_r_1089_, 4);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_r_1089_, 3);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_r_1089_, 2);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_r_1089_, 1);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_r_1089_, 0);
lean_dec(v_unused_1178_);
v___x_1111_ = v_r_1089_;
v_isShared_1112_ = v_isSharedCheck_1173_;
goto v_resetjp_1110_;
}
else
{
lean_dec(v_r_1089_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1173_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v_size_1113_; lean_object* v_k_1114_; lean_object* v_v_1115_; lean_object* v_l_1116_; lean_object* v_r_1117_; lean_object* v_size_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_size_1113_ = lean_ctor_get(v_l_1100_, 0);
v_k_1114_ = lean_ctor_get(v_l_1100_, 1);
v_v_1115_ = lean_ctor_get(v_l_1100_, 2);
v_l_1116_ = lean_ctor_get(v_l_1100_, 3);
v_r_1117_ = lean_ctor_get(v_l_1100_, 4);
v_size_1118_ = lean_ctor_get(v_r_1101_, 0);
v___x_1119_ = lean_unsigned_to_nat(2u);
v___x_1120_ = lean_nat_mul(v___x_1119_, v_size_1118_);
v___x_1121_ = lean_nat_dec_lt(v_size_1113_, v___x_1120_);
lean_dec(v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1149_; 
lean_inc(v_r_1117_);
lean_inc(v_l_1116_);
lean_inc(v_v_1115_);
lean_inc(v_k_1114_);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_l_1100_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; lean_object* v_unused_1153_; lean_object* v_unused_1154_; 
v_unused_1150_ = lean_ctor_get(v_l_1100_, 4);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_l_1100_, 3);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_l_1100_, 2);
lean_dec(v_unused_1152_);
v_unused_1153_ = lean_ctor_get(v_l_1100_, 1);
lean_dec(v_unused_1153_);
v_unused_1154_ = lean_ctor_get(v_l_1100_, 0);
lean_dec(v_unused_1154_);
v___x_1123_ = v_l_1100_;
v_isShared_1124_ = v_isSharedCheck_1149_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v_l_1100_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1149_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1139_; 
v___x_1125_ = lean_nat_add(v___x_1095_, v_size_1096_);
lean_dec(v_size_1096_);
v___x_1126_ = lean_nat_add(v___x_1125_, v_size_1097_);
lean_dec(v_size_1097_);
if (lean_obj_tag(v_l_1116_) == 0)
{
lean_object* v_size_1147_; 
v_size_1147_ = lean_ctor_get(v_l_1116_, 0);
lean_inc(v_size_1147_);
v___y_1139_ = v_size_1147_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_unsigned_to_nat(0u);
v___y_1139_ = v___x_1148_;
goto v___jp_1138_;
}
v___jp_1127_:
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = lean_nat_add(v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec(v___y_1129_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 4, v_r_1101_);
lean_ctor_set(v___x_1123_, 3, v_r_1117_);
lean_ctor_set(v___x_1123_, 2, v_v_1099_);
lean_ctor_set(v___x_1123_, 1, v_k_1098_);
lean_ctor_set(v___x_1123_, 0, v___x_1131_);
v___x_1133_ = v___x_1123_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v_r_1117_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_r_1101_);
v___x_1133_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1135_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 4, v___x_1133_);
lean_ctor_set(v___x_1111_, 3, v___y_1128_);
lean_ctor_set(v___x_1111_, 2, v_v_1115_);
lean_ctor_set(v___x_1111_, 1, v_k_1114_);
lean_ctor_set(v___x_1111_, 0, v___x_1126_);
v___x_1135_ = v___x_1111_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_k_1114_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_v_1115_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v___y_1128_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
v___jp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_nat_add(v___x_1125_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec(v___x_1125_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v_l_1116_);
lean_ctor_set(v___x_1091_, 3, v_impl_1094_);
lean_ctor_set(v___x_1091_, 0, v___x_1140_);
v___x_1142_ = v___x_1091_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_impl_1094_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v_l_1116_);
v___x_1142_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_nat_add(v___x_1095_, v_size_1118_);
if (lean_obj_tag(v_r_1117_) == 0)
{
lean_object* v_size_1144_; 
v_size_1144_ = lean_ctor_get(v_r_1117_, 0);
lean_inc(v_size_1144_);
v___y_1128_ = v___x_1142_;
v___y_1129_ = v___x_1143_;
v___y_1130_ = v_size_1144_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_unsigned_to_nat(0u);
v___y_1128_ = v___x_1142_;
v___y_1129_ = v___x_1143_;
v___y_1130_ = v___x_1145_;
goto v___jp_1127_;
}
}
}
}
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_del_object(v___x_1091_);
v___x_1155_ = lean_nat_add(v___x_1095_, v_size_1096_);
lean_dec(v_size_1096_);
v___x_1156_ = lean_nat_add(v___x_1155_, v_size_1097_);
lean_dec(v_size_1097_);
v___x_1157_ = lean_nat_add(v___x_1155_, v_size_1113_);
lean_dec(v___x_1155_);
lean_inc_ref(v_impl_1094_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 4, v_l_1100_);
lean_ctor_set(v___x_1111_, 3, v_impl_1094_);
lean_ctor_set(v___x_1111_, 2, v_v_1087_);
lean_ctor_set(v___x_1111_, 1, v_k_1086_);
lean_ctor_set(v___x_1111_, 0, v___x_1157_);
v___x_1159_ = v___x_1111_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_impl_1094_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v_l_1100_);
v___x_1159_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_isSharedCheck_1166_ = !lean_is_exclusive(v_impl_1094_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; lean_object* v_unused_1170_; lean_object* v_unused_1171_; 
v_unused_1167_ = lean_ctor_get(v_impl_1094_, 4);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_impl_1094_, 3);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_impl_1094_, 2);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_impl_1094_, 1);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_impl_1094_, 0);
lean_dec(v_unused_1171_);
v___x_1161_ = v_impl_1094_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v_impl_1094_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 4, v_r_1101_);
lean_ctor_set(v___x_1161_, 3, v___x_1159_);
lean_ctor_set(v___x_1161_, 2, v_v_1099_);
lean_ctor_set(v___x_1161_, 1, v_k_1098_);
lean_ctor_set(v___x_1161_, 0, v___x_1156_);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_k_1098_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_v_1099_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v_r_1101_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v_size_1179_ = lean_ctor_get(v_impl_1094_, 0);
lean_inc(v_size_1179_);
v___x_1180_ = lean_nat_add(v___x_1095_, v_size_1179_);
lean_dec(v_size_1179_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 3, v_impl_1094_);
lean_ctor_set(v___x_1091_, 0, v___x_1180_);
v___x_1182_ = v___x_1091_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_impl_1094_);
lean_ctor_set(v_reuseFailAlloc_1183_, 4, v_r_1089_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
else
{
if (lean_obj_tag(v_r_1089_) == 0)
{
lean_object* v_l_1184_; 
v_l_1184_ = lean_ctor_get(v_r_1089_, 3);
lean_inc(v_l_1184_);
if (lean_obj_tag(v_l_1184_) == 0)
{
lean_object* v_r_1185_; 
v_r_1185_ = lean_ctor_get(v_r_1089_, 4);
lean_inc(v_r_1185_);
if (lean_obj_tag(v_r_1185_) == 0)
{
lean_object* v_size_1186_; lean_object* v_k_1187_; lean_object* v_v_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1201_; 
v_size_1186_ = lean_ctor_get(v_r_1089_, 0);
v_k_1187_ = lean_ctor_get(v_r_1089_, 1);
v_v_1188_ = lean_ctor_get(v_r_1089_, 2);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_r_1089_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; lean_object* v_unused_1203_; 
v_unused_1202_ = lean_ctor_get(v_r_1089_, 4);
lean_dec(v_unused_1202_);
v_unused_1203_ = lean_ctor_get(v_r_1089_, 3);
lean_dec(v_unused_1203_);
v___x_1190_ = v_r_1089_;
v_isShared_1191_ = v_isSharedCheck_1201_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_v_1188_);
lean_inc(v_k_1187_);
lean_inc(v_size_1186_);
lean_dec(v_r_1089_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1201_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_size_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v_size_1192_ = lean_ctor_get(v_l_1184_, 0);
v___x_1193_ = lean_nat_add(v___x_1095_, v_size_1186_);
lean_dec(v_size_1186_);
v___x_1194_ = lean_nat_add(v___x_1095_, v_size_1192_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 4, v_l_1184_);
lean_ctor_set(v___x_1190_, 3, v_impl_1094_);
lean_ctor_set(v___x_1190_, 2, v_v_1087_);
lean_ctor_set(v___x_1190_, 1, v_k_1086_);
lean_ctor_set(v___x_1190_, 0, v___x_1194_);
v___x_1196_ = v___x_1190_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_impl_1094_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_l_1184_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v_r_1185_);
lean_ctor_set(v___x_1091_, 3, v___x_1196_);
lean_ctor_set(v___x_1091_, 2, v_v_1188_);
lean_ctor_set(v___x_1091_, 1, v_k_1187_);
lean_ctor_set(v___x_1091_, 0, v___x_1193_);
v___x_1198_ = v___x_1091_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_k_1187_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_v_1188_);
lean_ctor_set(v_reuseFailAlloc_1199_, 3, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1199_, 4, v_r_1185_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v_k_1204_; lean_object* v_v_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1228_; 
v_k_1204_ = lean_ctor_get(v_r_1089_, 1);
v_v_1205_ = lean_ctor_get(v_r_1089_, 2);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_r_1089_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; lean_object* v_unused_1230_; lean_object* v_unused_1231_; 
v_unused_1229_ = lean_ctor_get(v_r_1089_, 4);
lean_dec(v_unused_1229_);
v_unused_1230_ = lean_ctor_get(v_r_1089_, 3);
lean_dec(v_unused_1230_);
v_unused_1231_ = lean_ctor_get(v_r_1089_, 0);
lean_dec(v_unused_1231_);
v___x_1207_ = v_r_1089_;
v_isShared_1208_ = v_isSharedCheck_1228_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_v_1205_);
lean_inc(v_k_1204_);
lean_dec(v_r_1089_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1228_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_k_1209_; lean_object* v_v_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1224_; 
v_k_1209_ = lean_ctor_get(v_l_1184_, 1);
v_v_1210_ = lean_ctor_get(v_l_1184_, 2);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_l_1184_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; lean_object* v_unused_1226_; lean_object* v_unused_1227_; 
v_unused_1225_ = lean_ctor_get(v_l_1184_, 4);
lean_dec(v_unused_1225_);
v_unused_1226_ = lean_ctor_get(v_l_1184_, 3);
lean_dec(v_unused_1226_);
v_unused_1227_ = lean_ctor_get(v_l_1184_, 0);
lean_dec(v_unused_1227_);
v___x_1212_ = v_l_1184_;
v_isShared_1213_ = v_isSharedCheck_1224_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_v_1210_);
lean_inc(v_k_1209_);
lean_dec(v_l_1184_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1224_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = lean_unsigned_to_nat(3u);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 4, v_r_1185_);
lean_ctor_set(v___x_1212_, 3, v_r_1185_);
lean_ctor_set(v___x_1212_, 2, v_v_1087_);
lean_ctor_set(v___x_1212_, 1, v_k_1086_);
lean_ctor_set(v___x_1212_, 0, v___x_1095_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v_r_1185_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_r_1185_);
v___x_1216_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 3, v_r_1185_);
lean_ctor_set(v___x_1207_, 0, v___x_1095_);
v___x_1218_ = v___x_1207_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_k_1204_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_v_1205_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_r_1185_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_r_1185_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1220_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v___x_1218_);
lean_ctor_set(v___x_1091_, 3, v___x_1216_);
lean_ctor_set(v___x_1091_, 2, v_v_1210_);
lean_ctor_set(v___x_1091_, 1, v_k_1209_);
lean_ctor_set(v___x_1091_, 0, v___x_1214_);
v___x_1220_ = v___x_1091_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_k_1209_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_v_1210_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1232_; 
v_r_1232_ = lean_ctor_get(v_r_1089_, 4);
lean_inc(v_r_1232_);
if (lean_obj_tag(v_r_1232_) == 0)
{
lean_object* v_k_1233_; lean_object* v_v_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1245_; 
v_k_1233_ = lean_ctor_get(v_r_1089_, 1);
v_v_1234_ = lean_ctor_get(v_r_1089_, 2);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_r_1089_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; lean_object* v_unused_1247_; lean_object* v_unused_1248_; 
v_unused_1246_ = lean_ctor_get(v_r_1089_, 4);
lean_dec(v_unused_1246_);
v_unused_1247_ = lean_ctor_get(v_r_1089_, 3);
lean_dec(v_unused_1247_);
v_unused_1248_ = lean_ctor_get(v_r_1089_, 0);
lean_dec(v_unused_1248_);
v___x_1236_ = v_r_1089_;
v_isShared_1237_ = v_isSharedCheck_1245_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_v_1234_);
lean_inc(v_k_1233_);
lean_dec(v_r_1089_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1245_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = lean_unsigned_to_nat(3u);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 4, v_l_1184_);
lean_ctor_set(v___x_1236_, 2, v_v_1087_);
lean_ctor_set(v___x_1236_, 1, v_k_1086_);
lean_ctor_set(v___x_1236_, 0, v___x_1095_);
v___x_1240_ = v___x_1236_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_l_1184_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v_l_1184_);
v___x_1240_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1242_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v_r_1232_);
lean_ctor_set(v___x_1091_, 3, v___x_1240_);
lean_ctor_set(v___x_1091_, 2, v_v_1234_);
lean_ctor_set(v___x_1091_, 1, v_k_1233_);
lean_ctor_set(v___x_1091_, 0, v___x_1238_);
v___x_1242_ = v___x_1091_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_k_1233_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_v_1234_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_r_1232_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v_size_1249_; lean_object* v_k_1250_; lean_object* v_v_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1262_; 
v_size_1249_ = lean_ctor_get(v_r_1089_, 0);
v_k_1250_ = lean_ctor_get(v_r_1089_, 1);
v_v_1251_ = lean_ctor_get(v_r_1089_, 2);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_r_1089_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; lean_object* v_unused_1264_; 
v_unused_1263_ = lean_ctor_get(v_r_1089_, 4);
lean_dec(v_unused_1263_);
v_unused_1264_ = lean_ctor_get(v_r_1089_, 3);
lean_dec(v_unused_1264_);
v___x_1253_ = v_r_1089_;
v_isShared_1254_ = v_isSharedCheck_1262_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_v_1251_);
lean_inc(v_k_1250_);
lean_inc(v_size_1249_);
lean_dec(v_r_1089_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1262_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 3, v_r_1232_);
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_size_1249_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_r_1232_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_r_1232_);
v___x_1256_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = lean_unsigned_to_nat(2u);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v___x_1256_);
lean_ctor_set(v___x_1091_, 3, v_r_1232_);
lean_ctor_set(v___x_1091_, 0, v___x_1257_);
v___x_1259_ = v___x_1091_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_r_1232_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v___x_1256_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
else
{
lean_object* v___x_1266_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 3, v_r_1089_);
lean_ctor_set(v___x_1091_, 0, v___x_1095_);
v___x_1266_ = v___x_1091_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_r_1089_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_r_1089_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1091_);
lean_dec(v_v_1087_);
lean_dec(v_k_1086_);
if (lean_obj_tag(v_l_1088_) == 0)
{
if (lean_obj_tag(v_r_1089_) == 0)
{
lean_object* v_size_1268_; lean_object* v_k_1269_; lean_object* v_v_1270_; lean_object* v_l_1271_; lean_object* v_r_1272_; lean_object* v_size_1273_; lean_object* v_k_1274_; lean_object* v_v_1275_; lean_object* v_l_1276_; lean_object* v_r_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_size_1268_ = lean_ctor_get(v_l_1088_, 0);
v_k_1269_ = lean_ctor_get(v_l_1088_, 1);
v_v_1270_ = lean_ctor_get(v_l_1088_, 2);
v_l_1271_ = lean_ctor_get(v_l_1088_, 3);
v_r_1272_ = lean_ctor_get(v_l_1088_, 4);
lean_inc(v_r_1272_);
v_size_1273_ = lean_ctor_get(v_r_1089_, 0);
v_k_1274_ = lean_ctor_get(v_r_1089_, 1);
v_v_1275_ = lean_ctor_get(v_r_1089_, 2);
v_l_1276_ = lean_ctor_get(v_r_1089_, 3);
lean_inc(v_l_1276_);
v_r_1277_ = lean_ctor_get(v_r_1089_, 4);
v___x_1278_ = lean_unsigned_to_nat(1u);
v___x_1279_ = lean_nat_dec_lt(v_size_1268_, v_size_1273_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1415_; 
lean_inc(v_l_1271_);
lean_inc(v_v_1270_);
lean_inc(v_k_1269_);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_l_1088_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; lean_object* v_unused_1417_; lean_object* v_unused_1418_; lean_object* v_unused_1419_; lean_object* v_unused_1420_; 
v_unused_1416_ = lean_ctor_get(v_l_1088_, 4);
lean_dec(v_unused_1416_);
v_unused_1417_ = lean_ctor_get(v_l_1088_, 3);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v_l_1088_, 2);
lean_dec(v_unused_1418_);
v_unused_1419_ = lean_ctor_get(v_l_1088_, 1);
lean_dec(v_unused_1419_);
v_unused_1420_ = lean_ctor_get(v_l_1088_, 0);
lean_dec(v_unused_1420_);
v___x_1281_ = v_l_1088_;
v_isShared_1282_ = v_isSharedCheck_1415_;
goto v_resetjp_1280_;
}
else
{
lean_dec(v_l_1088_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1415_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v_tree_1284_; 
v___x_1283_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1269_, v_v_1270_, v_l_1271_, v_r_1272_);
v_tree_1284_ = lean_ctor_get(v___x_1283_, 2);
lean_inc(v_tree_1284_);
if (lean_obj_tag(v_tree_1284_) == 0)
{
lean_object* v_k_1285_; lean_object* v_v_1286_; lean_object* v_size_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_k_1285_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_k_1285_);
v_v_1286_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_v_1286_);
lean_dec_ref(v___x_1283_);
v_size_1287_ = lean_ctor_get(v_tree_1284_, 0);
v___x_1288_ = lean_unsigned_to_nat(3u);
v___x_1289_ = lean_nat_mul(v___x_1288_, v_size_1287_);
v___x_1290_ = lean_nat_dec_lt(v___x_1289_, v_size_1273_);
lean_dec(v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
lean_dec(v_l_1276_);
v___x_1291_ = lean_nat_add(v___x_1278_, v_size_1287_);
v___x_1292_ = lean_nat_add(v___x_1291_, v_size_1273_);
lean_dec(v___x_1291_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v_r_1089_);
lean_ctor_set(v___x_1281_, 3, v_tree_1284_);
lean_ctor_set(v___x_1281_, 2, v_v_1286_);
lean_ctor_set(v___x_1281_, 1, v_k_1285_);
lean_ctor_set(v___x_1281_, 0, v___x_1292_);
v___x_1294_ = v___x_1281_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_k_1285_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_v_1286_);
lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_tree_1284_);
lean_ctor_set(v_reuseFailAlloc_1295_, 4, v_r_1089_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
else
{
lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1350_; 
lean_inc(v_r_1277_);
lean_inc(v_v_1275_);
lean_inc(v_k_1274_);
lean_inc(v_size_1273_);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_r_1089_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; lean_object* v_unused_1355_; 
v_unused_1351_ = lean_ctor_get(v_r_1089_, 4);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_r_1089_, 3);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_r_1089_, 2);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_r_1089_, 1);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_r_1089_, 0);
lean_dec(v_unused_1355_);
v___x_1297_ = v_r_1089_;
v_isShared_1298_ = v_isSharedCheck_1350_;
goto v_resetjp_1296_;
}
else
{
lean_dec(v_r_1089_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1350_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v_size_1299_; lean_object* v_k_1300_; lean_object* v_v_1301_; lean_object* v_l_1302_; lean_object* v_r_1303_; lean_object* v_size_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_size_1299_ = lean_ctor_get(v_l_1276_, 0);
v_k_1300_ = lean_ctor_get(v_l_1276_, 1);
v_v_1301_ = lean_ctor_get(v_l_1276_, 2);
v_l_1302_ = lean_ctor_get(v_l_1276_, 3);
v_r_1303_ = lean_ctor_get(v_l_1276_, 4);
v_size_1304_ = lean_ctor_get(v_r_1277_, 0);
v___x_1305_ = lean_unsigned_to_nat(2u);
v___x_1306_ = lean_nat_mul(v___x_1305_, v_size_1304_);
v___x_1307_ = lean_nat_dec_lt(v_size_1299_, v___x_1306_);
lean_dec(v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1335_; 
lean_inc(v_r_1303_);
lean_inc(v_l_1302_);
lean_inc(v_v_1301_);
lean_inc(v_k_1300_);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_l_1276_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; lean_object* v_unused_1337_; lean_object* v_unused_1338_; lean_object* v_unused_1339_; lean_object* v_unused_1340_; 
v_unused_1336_ = lean_ctor_get(v_l_1276_, 4);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_l_1276_, 3);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v_l_1276_, 2);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_l_1276_, 1);
lean_dec(v_unused_1339_);
v_unused_1340_ = lean_ctor_get(v_l_1276_, 0);
lean_dec(v_unused_1340_);
v___x_1309_ = v_l_1276_;
v_isShared_1310_ = v_isSharedCheck_1335_;
goto v_resetjp_1308_;
}
else
{
lean_dec(v_l_1276_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1335_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1325_; 
v___x_1311_ = lean_nat_add(v___x_1278_, v_size_1287_);
v___x_1312_ = lean_nat_add(v___x_1311_, v_size_1273_);
lean_dec(v_size_1273_);
if (lean_obj_tag(v_l_1302_) == 0)
{
lean_object* v_size_1333_; 
v_size_1333_ = lean_ctor_get(v_l_1302_, 0);
lean_inc(v_size_1333_);
v___y_1325_ = v_size_1333_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___y_1325_ = v___x_1334_;
goto v___jp_1324_;
}
v___jp_1313_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = lean_nat_add(v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 4, v_r_1277_);
lean_ctor_set(v___x_1309_, 3, v_r_1303_);
lean_ctor_set(v___x_1309_, 2, v_v_1275_);
lean_ctor_set(v___x_1309_, 1, v_k_1274_);
lean_ctor_set(v___x_1309_, 0, v___x_1317_);
v___x_1319_ = v___x_1309_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_k_1274_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_v_1275_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_r_1303_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_r_1277_);
v___x_1319_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1321_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 4, v___x_1319_);
lean_ctor_set(v___x_1297_, 3, v___y_1314_);
lean_ctor_set(v___x_1297_, 2, v_v_1301_);
lean_ctor_set(v___x_1297_, 1, v_k_1300_);
lean_ctor_set(v___x_1297_, 0, v___x_1312_);
v___x_1321_ = v___x_1297_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_k_1300_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_v_1301_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v___y_1314_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
v___jp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = lean_nat_add(v___x_1311_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec(v___x_1311_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v_l_1302_);
lean_ctor_set(v___x_1281_, 3, v_tree_1284_);
lean_ctor_set(v___x_1281_, 2, v_v_1286_);
lean_ctor_set(v___x_1281_, 1, v_k_1285_);
lean_ctor_set(v___x_1281_, 0, v___x_1326_);
v___x_1328_ = v___x_1281_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_k_1285_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_v_1286_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_tree_1284_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v_l_1302_);
v___x_1328_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_nat_add(v___x_1278_, v_size_1304_);
if (lean_obj_tag(v_r_1303_) == 0)
{
lean_object* v_size_1330_; 
v_size_1330_ = lean_ctor_get(v_r_1303_, 0);
lean_inc(v_size_1330_);
v___y_1314_ = v___x_1328_;
v___y_1315_ = v___x_1329_;
v___y_1316_ = v_size_1330_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_unsigned_to_nat(0u);
v___y_1314_ = v___x_1328_;
v___y_1315_ = v___x_1329_;
v___y_1316_ = v___x_1331_;
goto v___jp_1313_;
}
}
}
}
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1341_ = lean_nat_add(v___x_1278_, v_size_1287_);
v___x_1342_ = lean_nat_add(v___x_1341_, v_size_1273_);
lean_dec(v_size_1273_);
v___x_1343_ = lean_nat_add(v___x_1341_, v_size_1299_);
lean_dec(v___x_1341_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 4, v_l_1276_);
lean_ctor_set(v___x_1297_, 3, v_tree_1284_);
lean_ctor_set(v___x_1297_, 2, v_v_1286_);
lean_ctor_set(v___x_1297_, 1, v_k_1285_);
lean_ctor_set(v___x_1297_, 0, v___x_1343_);
v___x_1345_ = v___x_1297_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_1285_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_1286_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_tree_1284_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_l_1276_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v_r_1277_);
lean_ctor_set(v___x_1281_, 3, v___x_1345_);
lean_ctor_set(v___x_1281_, 2, v_v_1275_);
lean_ctor_set(v___x_1281_, 1, v_k_1274_);
lean_ctor_set(v___x_1281_, 0, v___x_1342_);
v___x_1347_ = v___x_1281_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_k_1274_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_v_1275_);
lean_ctor_set(v_reuseFailAlloc_1348_, 3, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1348_, 4, v_r_1277_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
}
else
{
lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1409_; 
lean_inc(v_r_1277_);
lean_inc(v_v_1275_);
lean_inc(v_k_1274_);
lean_inc(v_size_1273_);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_r_1089_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; lean_object* v_unused_1411_; lean_object* v_unused_1412_; lean_object* v_unused_1413_; lean_object* v_unused_1414_; 
v_unused_1410_ = lean_ctor_get(v_r_1089_, 4);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v_r_1089_, 3);
lean_dec(v_unused_1411_);
v_unused_1412_ = lean_ctor_get(v_r_1089_, 2);
lean_dec(v_unused_1412_);
v_unused_1413_ = lean_ctor_get(v_r_1089_, 1);
lean_dec(v_unused_1413_);
v_unused_1414_ = lean_ctor_get(v_r_1089_, 0);
lean_dec(v_unused_1414_);
v___x_1357_ = v_r_1089_;
v_isShared_1358_ = v_isSharedCheck_1409_;
goto v_resetjp_1356_;
}
else
{
lean_dec(v_r_1089_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1409_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
if (lean_obj_tag(v_l_1276_) == 0)
{
if (lean_obj_tag(v_r_1277_) == 0)
{
lean_object* v_k_1359_; lean_object* v_v_1360_; lean_object* v_size_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v_k_1359_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_k_1359_);
v_v_1360_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_v_1360_);
lean_dec_ref(v___x_1283_);
v_size_1361_ = lean_ctor_get(v_l_1276_, 0);
v___x_1362_ = lean_nat_add(v___x_1278_, v_size_1273_);
lean_dec(v_size_1273_);
v___x_1363_ = lean_nat_add(v___x_1278_, v_size_1361_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_l_1276_);
lean_ctor_set(v___x_1357_, 3, v_tree_1284_);
lean_ctor_set(v___x_1357_, 2, v_v_1360_);
lean_ctor_set(v___x_1357_, 1, v_k_1359_);
lean_ctor_set(v___x_1357_, 0, v___x_1363_);
v___x_1365_ = v___x_1357_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_k_1359_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_v_1360_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_tree_1284_);
lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_l_1276_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v_r_1277_);
lean_ctor_set(v___x_1281_, 3, v___x_1365_);
lean_ctor_set(v___x_1281_, 2, v_v_1275_);
lean_ctor_set(v___x_1281_, 1, v_k_1274_);
lean_ctor_set(v___x_1281_, 0, v___x_1362_);
v___x_1367_ = v___x_1281_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_k_1274_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_v_1275_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1368_, 4, v_r_1277_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
lean_object* v_k_1370_; lean_object* v_v_1371_; lean_object* v_k_1372_; lean_object* v_v_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v_size_1273_);
v_k_1370_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_k_1370_);
v_v_1371_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_v_1371_);
lean_dec_ref(v___x_1283_);
v_k_1372_ = lean_ctor_get(v_l_1276_, 1);
v_v_1373_ = lean_ctor_get(v_l_1276_, 2);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_l_1276_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; lean_object* v_unused_1389_; lean_object* v_unused_1390_; 
v_unused_1388_ = lean_ctor_get(v_l_1276_, 4);
lean_dec(v_unused_1388_);
v_unused_1389_ = lean_ctor_get(v_l_1276_, 3);
lean_dec(v_unused_1389_);
v_unused_1390_ = lean_ctor_get(v_l_1276_, 0);
lean_dec(v_unused_1390_);
v___x_1375_ = v_l_1276_;
v_isShared_1376_ = v_isSharedCheck_1387_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_v_1373_);
lean_inc(v_k_1372_);
lean_dec(v_l_1276_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1387_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = lean_unsigned_to_nat(3u);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_r_1277_);
lean_ctor_set(v___x_1375_, 3, v_r_1277_);
lean_ctor_set(v___x_1375_, 2, v_v_1371_);
lean_ctor_set(v___x_1375_, 1, v_k_1370_);
lean_ctor_set(v___x_1375_, 0, v___x_1278_);
v___x_1379_ = v___x_1375_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v_r_1277_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v_r_1277_);
v___x_1379_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1381_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 3, v_r_1277_);
lean_ctor_set(v___x_1357_, 0, v___x_1278_);
v___x_1381_ = v___x_1357_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_k_1274_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_v_1275_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v_r_1277_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v_r_1277_);
v___x_1381_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1383_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v___x_1381_);
lean_ctor_set(v___x_1281_, 3, v___x_1379_);
lean_ctor_set(v___x_1281_, 2, v_v_1373_);
lean_ctor_set(v___x_1281_, 1, v_k_1372_);
lean_ctor_set(v___x_1281_, 0, v___x_1377_);
v___x_1383_ = v___x_1281_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1277_) == 0)
{
lean_object* v_k_1391_; lean_object* v_v_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_dec(v_size_1273_);
v_k_1391_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_k_1391_);
v_v_1392_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_v_1392_);
lean_dec_ref(v___x_1283_);
v___x_1393_ = lean_unsigned_to_nat(3u);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_l_1276_);
lean_ctor_set(v___x_1357_, 2, v_v_1392_);
lean_ctor_set(v___x_1357_, 1, v_k_1391_);
lean_ctor_set(v___x_1357_, 0, v___x_1278_);
v___x_1395_ = v___x_1357_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_k_1391_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_v_1392_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_l_1276_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_l_1276_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1397_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v_r_1277_);
lean_ctor_set(v___x_1281_, 3, v___x_1395_);
lean_ctor_set(v___x_1281_, 2, v_v_1275_);
lean_ctor_set(v___x_1281_, 1, v_k_1274_);
lean_ctor_set(v___x_1281_, 0, v___x_1393_);
v___x_1397_ = v___x_1281_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_k_1274_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_v_1275_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v_r_1277_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
else
{
lean_object* v_k_1400_; lean_object* v_v_1401_; lean_object* v___x_1403_; 
v_k_1400_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_k_1400_);
v_v_1401_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_v_1401_);
lean_dec_ref(v___x_1283_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 3, v_r_1277_);
v___x_1403_ = v___x_1357_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_size_1273_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_k_1274_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_v_1275_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_r_1277_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_r_1277_);
v___x_1403_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = lean_unsigned_to_nat(2u);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v___x_1403_);
lean_ctor_set(v___x_1281_, 3, v_r_1277_);
lean_ctor_set(v___x_1281_, 2, v_v_1401_);
lean_ctor_set(v___x_1281_, 1, v_k_1400_);
lean_ctor_set(v___x_1281_, 0, v___x_1404_);
v___x_1406_ = v___x_1281_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_k_1400_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_v_1401_);
lean_ctor_set(v_reuseFailAlloc_1407_, 3, v_r_1277_);
lean_ctor_set(v_reuseFailAlloc_1407_, 4, v___x_1403_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
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
lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1573_; 
lean_inc(v_r_1277_);
lean_inc(v_v_1275_);
lean_inc(v_k_1274_);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_r_1089_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; lean_object* v_unused_1578_; 
v_unused_1574_ = lean_ctor_get(v_r_1089_, 4);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_r_1089_, 3);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_r_1089_, 2);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_r_1089_, 1);
lean_dec(v_unused_1577_);
v_unused_1578_ = lean_ctor_get(v_r_1089_, 0);
lean_dec(v_unused_1578_);
v___x_1422_ = v_r_1089_;
v_isShared_1423_ = v_isSharedCheck_1573_;
goto v_resetjp_1421_;
}
else
{
lean_dec(v_r_1089_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1573_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v_tree_1425_; 
v___x_1424_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1274_, v_v_1275_, v_l_1276_, v_r_1277_);
v_tree_1425_ = lean_ctor_get(v___x_1424_, 2);
lean_inc(v_tree_1425_);
if (lean_obj_tag(v_tree_1425_) == 0)
{
lean_object* v_k_1426_; lean_object* v_v_1427_; lean_object* v_size_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_k_1426_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_k_1426_);
v_v_1427_ = lean_ctor_get(v___x_1424_, 1);
lean_inc(v_v_1427_);
lean_dec_ref(v___x_1424_);
v_size_1428_ = lean_ctor_get(v_tree_1425_, 0);
v___x_1429_ = lean_unsigned_to_nat(3u);
v___x_1430_ = lean_nat_mul(v___x_1429_, v_size_1428_);
v___x_1431_ = lean_nat_dec_lt(v___x_1430_, v_size_1268_);
lean_dec(v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
lean_dec(v_r_1272_);
v___x_1432_ = lean_nat_add(v___x_1278_, v_size_1268_);
v___x_1433_ = lean_nat_add(v___x_1432_, v_size_1428_);
lean_dec(v___x_1432_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_tree_1425_);
lean_ctor_set(v___x_1422_, 3, v_l_1088_);
lean_ctor_set(v___x_1422_, 2, v_v_1427_);
lean_ctor_set(v___x_1422_, 1, v_k_1426_);
lean_ctor_set(v___x_1422_, 0, v___x_1433_);
v___x_1435_ = v___x_1422_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_k_1426_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_v_1427_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_l_1088_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v_tree_1425_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
else
{
lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1502_; 
lean_inc(v_l_1271_);
lean_inc(v_v_1270_);
lean_inc(v_k_1269_);
lean_inc(v_size_1268_);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_l_1088_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; 
v_unused_1503_ = lean_ctor_get(v_l_1088_, 4);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_l_1088_, 3);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_l_1088_, 2);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_l_1088_, 1);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_l_1088_, 0);
lean_dec(v_unused_1507_);
v___x_1438_ = v_l_1088_;
v_isShared_1439_ = v_isSharedCheck_1502_;
goto v_resetjp_1437_;
}
else
{
lean_dec(v_l_1088_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1502_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_size_1440_; lean_object* v_size_1441_; lean_object* v_k_1442_; lean_object* v_v_1443_; lean_object* v_l_1444_; lean_object* v_r_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v_size_1440_ = lean_ctor_get(v_l_1271_, 0);
v_size_1441_ = lean_ctor_get(v_r_1272_, 0);
v_k_1442_ = lean_ctor_get(v_r_1272_, 1);
v_v_1443_ = lean_ctor_get(v_r_1272_, 2);
v_l_1444_ = lean_ctor_get(v_r_1272_, 3);
v_r_1445_ = lean_ctor_get(v_r_1272_, 4);
v___x_1446_ = lean_unsigned_to_nat(2u);
v___x_1447_ = lean_nat_mul(v___x_1446_, v_size_1440_);
v___x_1448_ = lean_nat_dec_lt(v_size_1441_, v___x_1447_);
lean_dec(v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1486_; 
lean_inc(v_r_1445_);
lean_inc(v_l_1444_);
lean_inc(v_v_1443_);
lean_inc(v_k_1442_);
lean_del_object(v___x_1438_);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_r_1272_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; lean_object* v_unused_1488_; lean_object* v_unused_1489_; lean_object* v_unused_1490_; lean_object* v_unused_1491_; 
v_unused_1487_ = lean_ctor_get(v_r_1272_, 4);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_r_1272_, 3);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_r_1272_, 2);
lean_dec(v_unused_1489_);
v_unused_1490_ = lean_ctor_get(v_r_1272_, 1);
lean_dec(v_unused_1490_);
v_unused_1491_ = lean_ctor_get(v_r_1272_, 0);
lean_dec(v_unused_1491_);
v___x_1450_ = v_r_1272_;
v_isShared_1451_ = v_isSharedCheck_1486_;
goto v_resetjp_1449_;
}
else
{
lean_dec(v_r_1272_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1486_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___x_1474_; lean_object* v___y_1476_; 
v___x_1452_ = lean_nat_add(v___x_1278_, v_size_1268_);
lean_dec(v_size_1268_);
v___x_1453_ = lean_nat_add(v___x_1452_, v_size_1428_);
lean_dec(v___x_1452_);
v___x_1474_ = lean_nat_add(v___x_1278_, v_size_1440_);
if (lean_obj_tag(v_l_1444_) == 0)
{
lean_object* v_size_1484_; 
v_size_1484_ = lean_ctor_get(v_l_1444_, 0);
lean_inc(v_size_1484_);
v___y_1476_ = v_size_1484_;
goto v___jp_1475_;
}
else
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_unsigned_to_nat(0u);
v___y_1476_ = v___x_1485_;
goto v___jp_1475_;
}
v___jp_1454_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = lean_nat_add(v___y_1455_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec(v___y_1455_);
lean_inc_ref(v_tree_1425_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 4, v_tree_1425_);
lean_ctor_set(v___x_1450_, 3, v_r_1445_);
lean_ctor_set(v___x_1450_, 2, v_v_1427_);
lean_ctor_set(v___x_1450_, 1, v_k_1426_);
lean_ctor_set(v___x_1450_, 0, v___x_1458_);
v___x_1460_ = v___x_1450_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_k_1426_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_v_1427_);
lean_ctor_set(v_reuseFailAlloc_1473_, 3, v_r_1445_);
lean_ctor_set(v_reuseFailAlloc_1473_, 4, v_tree_1425_);
v___x_1460_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
v_isSharedCheck_1467_ = !lean_is_exclusive(v_tree_1425_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; 
v_unused_1468_ = lean_ctor_get(v_tree_1425_, 4);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_tree_1425_, 3);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_tree_1425_, 2);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_tree_1425_, 1);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_tree_1425_, 0);
lean_dec(v_unused_1472_);
v___x_1462_ = v_tree_1425_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_dec(v_tree_1425_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 4, v___x_1460_);
lean_ctor_set(v___x_1462_, 3, v___y_1456_);
lean_ctor_set(v___x_1462_, 2, v_v_1443_);
lean_ctor_set(v___x_1462_, 1, v_k_1442_);
lean_ctor_set(v___x_1462_, 0, v___x_1453_);
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_k_1442_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v_v_1443_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v___y_1456_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v___x_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
v___jp_1475_:
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1477_ = lean_nat_add(v___x_1474_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec(v___x_1474_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_l_1444_);
lean_ctor_set(v___x_1422_, 3, v_l_1271_);
lean_ctor_set(v___x_1422_, 2, v_v_1270_);
lean_ctor_set(v___x_1422_, 1, v_k_1269_);
lean_ctor_set(v___x_1422_, 0, v___x_1477_);
v___x_1479_ = v___x_1422_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_k_1269_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_v_1270_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v_l_1271_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v_l_1444_);
v___x_1479_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_nat_add(v___x_1278_, v_size_1428_);
if (lean_obj_tag(v_r_1445_) == 0)
{
lean_object* v_size_1481_; 
v_size_1481_ = lean_ctor_get(v_r_1445_, 0);
lean_inc(v_size_1481_);
v___y_1455_ = v___x_1480_;
v___y_1456_ = v___x_1479_;
v___y_1457_ = v_size_1481_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_unsigned_to_nat(0u);
v___y_1455_ = v___x_1480_;
v___y_1456_ = v___x_1479_;
v___y_1457_ = v___x_1482_;
goto v___jp_1454_;
}
}
}
}
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1492_ = lean_nat_add(v___x_1278_, v_size_1268_);
lean_dec(v_size_1268_);
v___x_1493_ = lean_nat_add(v___x_1492_, v_size_1428_);
lean_dec(v___x_1492_);
v___x_1494_ = lean_nat_add(v___x_1278_, v_size_1428_);
v___x_1495_ = lean_nat_add(v___x_1494_, v_size_1441_);
lean_dec(v___x_1494_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_tree_1425_);
lean_ctor_set(v___x_1422_, 3, v_r_1272_);
lean_ctor_set(v___x_1422_, 2, v_v_1427_);
lean_ctor_set(v___x_1422_, 1, v_k_1426_);
lean_ctor_set(v___x_1422_, 0, v___x_1495_);
v___x_1497_ = v___x_1422_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1426_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1427_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_r_1272_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_tree_1425_);
v___x_1497_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 4, v___x_1497_);
lean_ctor_set(v___x_1438_, 0, v___x_1493_);
v___x_1499_ = v___x_1438_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1269_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1270_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1271_);
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
}
}
}
else
{
if (lean_obj_tag(v_l_1271_) == 0)
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1531_; 
lean_inc_ref(v_l_1271_);
lean_inc(v_v_1270_);
lean_inc(v_k_1269_);
lean_inc(v_size_1268_);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_l_1088_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; 
v_unused_1532_ = lean_ctor_get(v_l_1088_, 4);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_l_1088_, 3);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_l_1088_, 2);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_l_1088_, 1);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_l_1088_, 0);
lean_dec(v_unused_1536_);
v___x_1509_ = v_l_1088_;
v_isShared_1510_ = v_isSharedCheck_1531_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v_l_1088_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1531_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
if (lean_obj_tag(v_r_1272_) == 0)
{
lean_object* v_k_1511_; lean_object* v_v_1512_; lean_object* v_size_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v_k_1511_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_k_1511_);
v_v_1512_ = lean_ctor_get(v___x_1424_, 1);
lean_inc(v_v_1512_);
lean_dec_ref(v___x_1424_);
v_size_1513_ = lean_ctor_get(v_r_1272_, 0);
v___x_1514_ = lean_nat_add(v___x_1278_, v_size_1268_);
lean_dec(v_size_1268_);
v___x_1515_ = lean_nat_add(v___x_1278_, v_size_1513_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_tree_1425_);
lean_ctor_set(v___x_1422_, 3, v_r_1272_);
lean_ctor_set(v___x_1422_, 2, v_v_1512_);
lean_ctor_set(v___x_1422_, 1, v_k_1511_);
lean_ctor_set(v___x_1422_, 0, v___x_1515_);
v___x_1517_ = v___x_1422_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_k_1511_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_v_1512_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_r_1272_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_tree_1425_);
v___x_1517_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 4, v___x_1517_);
lean_ctor_set(v___x_1509_, 0, v___x_1514_);
v___x_1519_ = v___x_1509_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_k_1269_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_v_1270_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_l_1271_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
else
{
lean_object* v_k_1522_; lean_object* v_v_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
lean_dec(v_size_1268_);
v_k_1522_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_k_1522_);
v_v_1523_ = lean_ctor_get(v___x_1424_, 1);
lean_inc(v_v_1523_);
lean_dec_ref(v___x_1424_);
v___x_1524_ = lean_unsigned_to_nat(3u);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_r_1272_);
lean_ctor_set(v___x_1422_, 3, v_r_1272_);
lean_ctor_set(v___x_1422_, 2, v_v_1523_);
lean_ctor_set(v___x_1422_, 1, v_k_1522_);
lean_ctor_set(v___x_1422_, 0, v___x_1278_);
v___x_1526_ = v___x_1422_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1522_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1523_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_r_1272_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_r_1272_);
v___x_1526_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1528_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 4, v___x_1526_);
lean_ctor_set(v___x_1509_, 0, v___x_1524_);
v___x_1528_ = v___x_1509_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1269_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1270_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_l_1271_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1272_) == 0)
{
lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1561_; 
lean_inc(v_l_1271_);
lean_inc(v_v_1270_);
lean_inc(v_k_1269_);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_l_1088_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; lean_object* v_unused_1563_; lean_object* v_unused_1564_; lean_object* v_unused_1565_; lean_object* v_unused_1566_; 
v_unused_1562_ = lean_ctor_get(v_l_1088_, 4);
lean_dec(v_unused_1562_);
v_unused_1563_ = lean_ctor_get(v_l_1088_, 3);
lean_dec(v_unused_1563_);
v_unused_1564_ = lean_ctor_get(v_l_1088_, 2);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v_l_1088_, 1);
lean_dec(v_unused_1565_);
v_unused_1566_ = lean_ctor_get(v_l_1088_, 0);
lean_dec(v_unused_1566_);
v___x_1538_ = v_l_1088_;
v_isShared_1539_ = v_isSharedCheck_1561_;
goto v_resetjp_1537_;
}
else
{
lean_dec(v_l_1088_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1561_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v_k_1540_; lean_object* v_v_1541_; lean_object* v_k_1542_; lean_object* v_v_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1557_; 
v_k_1540_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_k_1540_);
v_v_1541_ = lean_ctor_get(v___x_1424_, 1);
lean_inc(v_v_1541_);
lean_dec_ref(v___x_1424_);
v_k_1542_ = lean_ctor_get(v_r_1272_, 1);
v_v_1543_ = lean_ctor_get(v_r_1272_, 2);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_r_1272_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; lean_object* v_unused_1559_; lean_object* v_unused_1560_; 
v_unused_1558_ = lean_ctor_get(v_r_1272_, 4);
lean_dec(v_unused_1558_);
v_unused_1559_ = lean_ctor_get(v_r_1272_, 3);
lean_dec(v_unused_1559_);
v_unused_1560_ = lean_ctor_get(v_r_1272_, 0);
lean_dec(v_unused_1560_);
v___x_1545_ = v_r_1272_;
v_isShared_1546_ = v_isSharedCheck_1557_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_v_1543_);
lean_inc(v_k_1542_);
lean_dec(v_r_1272_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1557_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = lean_unsigned_to_nat(3u);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 4, v_l_1271_);
lean_ctor_set(v___x_1545_, 3, v_l_1271_);
lean_ctor_set(v___x_1545_, 2, v_v_1270_);
lean_ctor_set(v___x_1545_, 1, v_k_1269_);
lean_ctor_set(v___x_1545_, 0, v___x_1278_);
v___x_1549_ = v___x_1545_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_k_1269_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_v_1270_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v_l_1271_);
lean_ctor_set(v_reuseFailAlloc_1556_, 4, v_l_1271_);
v___x_1549_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_l_1271_);
lean_ctor_set(v___x_1422_, 3, v_l_1271_);
lean_ctor_set(v___x_1422_, 2, v_v_1541_);
lean_ctor_set(v___x_1422_, 1, v_k_1540_);
lean_ctor_set(v___x_1422_, 0, v___x_1278_);
v___x_1551_ = v___x_1422_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_k_1540_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_v_1541_);
lean_ctor_set(v_reuseFailAlloc_1555_, 3, v_l_1271_);
lean_ctor_set(v_reuseFailAlloc_1555_, 4, v_l_1271_);
v___x_1551_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1553_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v___x_1551_);
lean_ctor_set(v___x_1538_, 3, v___x_1549_);
lean_ctor_set(v___x_1538_, 2, v_v_1543_);
lean_ctor_set(v___x_1538_, 1, v_k_1542_);
lean_ctor_set(v___x_1538_, 0, v___x_1547_);
v___x_1553_ = v___x_1538_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_k_1542_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_v_1543_);
lean_ctor_set(v_reuseFailAlloc_1554_, 3, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1554_, 4, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
}
else
{
lean_object* v_k_1567_; lean_object* v_v_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v_k_1567_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_k_1567_);
v_v_1568_ = lean_ctor_get(v___x_1424_, 1);
lean_inc(v_v_1568_);
lean_dec_ref(v___x_1424_);
v___x_1569_ = lean_unsigned_to_nat(2u);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v_r_1272_);
lean_ctor_set(v___x_1422_, 3, v_l_1088_);
lean_ctor_set(v___x_1422_, 2, v_v_1568_);
lean_ctor_set(v___x_1422_, 1, v_k_1567_);
lean_ctor_set(v___x_1422_, 0, v___x_1569_);
v___x_1571_ = v___x_1422_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_k_1567_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_v_1568_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_l_1088_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_r_1272_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
}
else
{
return v_l_1088_;
}
}
else
{
return v_r_1089_;
}
}
default: 
{
lean_object* v_impl_1579_; lean_object* v___x_1580_; 
v_impl_1579_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1084_, v_r_1089_);
v___x_1580_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1579_) == 0)
{
if (lean_obj_tag(v_l_1088_) == 0)
{
lean_object* v_size_1581_; lean_object* v_size_1582_; lean_object* v_k_1583_; lean_object* v_v_1584_; lean_object* v_l_1585_; lean_object* v_r_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v_size_1581_ = lean_ctor_get(v_impl_1579_, 0);
lean_inc(v_size_1581_);
v_size_1582_ = lean_ctor_get(v_l_1088_, 0);
v_k_1583_ = lean_ctor_get(v_l_1088_, 1);
v_v_1584_ = lean_ctor_get(v_l_1088_, 2);
v_l_1585_ = lean_ctor_get(v_l_1088_, 3);
v_r_1586_ = lean_ctor_get(v_l_1088_, 4);
lean_inc(v_r_1586_);
v___x_1587_ = lean_unsigned_to_nat(3u);
v___x_1588_ = lean_nat_mul(v___x_1587_, v_size_1581_);
v___x_1589_ = lean_nat_dec_lt(v___x_1588_, v_size_1582_);
lean_dec(v___x_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
lean_dec(v_r_1586_);
v___x_1590_ = lean_nat_add(v___x_1580_, v_size_1582_);
v___x_1591_ = lean_nat_add(v___x_1590_, v_size_1581_);
lean_dec(v_size_1581_);
lean_dec(v___x_1590_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v_impl_1579_);
lean_ctor_set(v___x_1091_, 0, v___x_1591_);
v___x_1593_ = v___x_1091_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_l_1088_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_impl_1579_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
else
{
lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1660_; 
lean_inc(v_l_1585_);
lean_inc(v_v_1584_);
lean_inc(v_k_1583_);
lean_inc(v_size_1582_);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_l_1088_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; lean_object* v_unused_1664_; lean_object* v_unused_1665_; 
v_unused_1661_ = lean_ctor_get(v_l_1088_, 4);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_l_1088_, 3);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_l_1088_, 2);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v_l_1088_, 1);
lean_dec(v_unused_1664_);
v_unused_1665_ = lean_ctor_get(v_l_1088_, 0);
lean_dec(v_unused_1665_);
v___x_1596_ = v_l_1088_;
v_isShared_1597_ = v_isSharedCheck_1660_;
goto v_resetjp_1595_;
}
else
{
lean_dec(v_l_1088_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1660_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_size_1598_; lean_object* v_size_1599_; lean_object* v_k_1600_; lean_object* v_v_1601_; lean_object* v_l_1602_; lean_object* v_r_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v_size_1598_ = lean_ctor_get(v_l_1585_, 0);
v_size_1599_ = lean_ctor_get(v_r_1586_, 0);
v_k_1600_ = lean_ctor_get(v_r_1586_, 1);
v_v_1601_ = lean_ctor_get(v_r_1586_, 2);
v_l_1602_ = lean_ctor_get(v_r_1586_, 3);
v_r_1603_ = lean_ctor_get(v_r_1586_, 4);
v___x_1604_ = lean_unsigned_to_nat(2u);
v___x_1605_ = lean_nat_mul(v___x_1604_, v_size_1598_);
v___x_1606_ = lean_nat_dec_lt(v_size_1599_, v___x_1605_);
lean_dec(v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1635_; 
lean_inc(v_r_1603_);
lean_inc(v_l_1602_);
lean_inc(v_v_1601_);
lean_inc(v_k_1600_);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_r_1586_);
if (v_isSharedCheck_1635_ == 0)
{
lean_object* v_unused_1636_; lean_object* v_unused_1637_; lean_object* v_unused_1638_; lean_object* v_unused_1639_; lean_object* v_unused_1640_; 
v_unused_1636_ = lean_ctor_get(v_r_1586_, 4);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_r_1586_, 3);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_r_1586_, 2);
lean_dec(v_unused_1638_);
v_unused_1639_ = lean_ctor_get(v_r_1586_, 1);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_r_1586_, 0);
lean_dec(v_unused_1640_);
v___x_1608_ = v_r_1586_;
v_isShared_1609_ = v_isSharedCheck_1635_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v_r_1586_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1635_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___x_1623_; lean_object* v___y_1625_; 
v___x_1610_ = lean_nat_add(v___x_1580_, v_size_1582_);
lean_dec(v_size_1582_);
v___x_1611_ = lean_nat_add(v___x_1610_, v_size_1581_);
lean_dec(v___x_1610_);
v___x_1623_ = lean_nat_add(v___x_1580_, v_size_1598_);
if (lean_obj_tag(v_l_1602_) == 0)
{
lean_object* v_size_1633_; 
v_size_1633_ = lean_ctor_get(v_l_1602_, 0);
lean_inc(v_size_1633_);
v___y_1625_ = v_size_1633_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_unsigned_to_nat(0u);
v___y_1625_ = v___x_1634_;
goto v___jp_1624_;
}
v___jp_1612_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1616_ = lean_nat_add(v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec(v___y_1614_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 4, v_impl_1579_);
lean_ctor_set(v___x_1608_, 3, v_r_1603_);
lean_ctor_set(v___x_1608_, 2, v_v_1087_);
lean_ctor_set(v___x_1608_, 1, v_k_1086_);
lean_ctor_set(v___x_1608_, 0, v___x_1616_);
v___x_1618_ = v___x_1608_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v_r_1603_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v_impl_1579_);
v___x_1618_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1620_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 4, v___x_1618_);
lean_ctor_set(v___x_1596_, 3, v___y_1613_);
lean_ctor_set(v___x_1596_, 2, v_v_1601_);
lean_ctor_set(v___x_1596_, 1, v_k_1600_);
lean_ctor_set(v___x_1596_, 0, v___x_1611_);
v___x_1620_ = v___x_1596_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_k_1600_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_v_1601_);
lean_ctor_set(v_reuseFailAlloc_1621_, 3, v___y_1613_);
lean_ctor_set(v_reuseFailAlloc_1621_, 4, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
v___jp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1626_ = lean_nat_add(v___x_1623_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec(v___x_1623_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v_l_1602_);
lean_ctor_set(v___x_1091_, 3, v_l_1585_);
lean_ctor_set(v___x_1091_, 2, v_v_1584_);
lean_ctor_set(v___x_1091_, 1, v_k_1583_);
lean_ctor_set(v___x_1091_, 0, v___x_1626_);
v___x_1628_ = v___x_1091_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_k_1583_);
lean_ctor_set(v_reuseFailAlloc_1632_, 2, v_v_1584_);
lean_ctor_set(v_reuseFailAlloc_1632_, 3, v_l_1585_);
lean_ctor_set(v_reuseFailAlloc_1632_, 4, v_l_1602_);
v___x_1628_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_nat_add(v___x_1580_, v_size_1581_);
lean_dec(v_size_1581_);
if (lean_obj_tag(v_r_1603_) == 0)
{
lean_object* v_size_1630_; 
v_size_1630_ = lean_ctor_get(v_r_1603_, 0);
lean_inc(v_size_1630_);
v___y_1613_ = v___x_1628_;
v___y_1614_ = v___x_1629_;
v___y_1615_ = v_size_1630_;
goto v___jp_1612_;
}
else
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_unsigned_to_nat(0u);
v___y_1613_ = v___x_1628_;
v___y_1614_ = v___x_1629_;
v___y_1615_ = v___x_1631_;
goto v___jp_1612_;
}
}
}
}
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
lean_del_object(v___x_1091_);
v___x_1641_ = lean_nat_add(v___x_1580_, v_size_1582_);
lean_dec(v_size_1582_);
v___x_1642_ = lean_nat_add(v___x_1641_, v_size_1581_);
lean_dec(v___x_1641_);
v___x_1643_ = lean_nat_add(v___x_1580_, v_size_1581_);
lean_dec(v_size_1581_);
v___x_1644_ = lean_nat_add(v___x_1643_, v_size_1599_);
lean_dec(v___x_1643_);
lean_inc_ref(v_impl_1579_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 4, v_impl_1579_);
lean_ctor_set(v___x_1596_, 3, v_r_1586_);
lean_ctor_set(v___x_1596_, 2, v_v_1087_);
lean_ctor_set(v___x_1596_, 1, v_k_1086_);
lean_ctor_set(v___x_1596_, 0, v___x_1644_);
v___x_1646_ = v___x_1596_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1659_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1659_, 3, v_r_1586_);
lean_ctor_set(v_reuseFailAlloc_1659_, 4, v_impl_1579_);
v___x_1646_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_isSharedCheck_1653_ = !lean_is_exclusive(v_impl_1579_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; lean_object* v_unused_1655_; lean_object* v_unused_1656_; lean_object* v_unused_1657_; lean_object* v_unused_1658_; 
v_unused_1654_ = lean_ctor_get(v_impl_1579_, 4);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_impl_1579_, 3);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_impl_1579_, 2);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_impl_1579_, 1);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_impl_1579_, 0);
lean_dec(v_unused_1658_);
v___x_1648_ = v_impl_1579_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_dec(v_impl_1579_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 4, v___x_1646_);
lean_ctor_set(v___x_1648_, 3, v_l_1585_);
lean_ctor_set(v___x_1648_, 2, v_v_1584_);
lean_ctor_set(v___x_1648_, 1, v_k_1583_);
lean_ctor_set(v___x_1648_, 0, v___x_1642_);
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_k_1583_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_v_1584_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_l_1585_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v___x_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v_size_1666_ = lean_ctor_get(v_impl_1579_, 0);
lean_inc(v_size_1666_);
v___x_1667_ = lean_nat_add(v___x_1580_, v_size_1666_);
lean_dec(v_size_1666_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v_impl_1579_);
lean_ctor_set(v___x_1091_, 0, v___x_1667_);
v___x_1669_ = v___x_1091_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v_l_1088_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v_impl_1579_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
else
{
if (lean_obj_tag(v_l_1088_) == 0)
{
lean_object* v_l_1671_; 
v_l_1671_ = lean_ctor_get(v_l_1088_, 3);
if (lean_obj_tag(v_l_1671_) == 0)
{
lean_object* v_r_1672_; 
lean_inc_ref(v_l_1671_);
v_r_1672_ = lean_ctor_get(v_l_1088_, 4);
lean_inc(v_r_1672_);
if (lean_obj_tag(v_r_1672_) == 0)
{
lean_object* v_size_1673_; lean_object* v_k_1674_; lean_object* v_v_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1688_; 
v_size_1673_ = lean_ctor_get(v_l_1088_, 0);
v_k_1674_ = lean_ctor_get(v_l_1088_, 1);
v_v_1675_ = lean_ctor_get(v_l_1088_, 2);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_l_1088_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; lean_object* v_unused_1690_; 
v_unused_1689_ = lean_ctor_get(v_l_1088_, 4);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_l_1088_, 3);
lean_dec(v_unused_1690_);
v___x_1677_ = v_l_1088_;
v_isShared_1678_ = v_isSharedCheck_1688_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_v_1675_);
lean_inc(v_k_1674_);
lean_inc(v_size_1673_);
lean_dec(v_l_1088_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1688_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v_size_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
v_size_1679_ = lean_ctor_get(v_r_1672_, 0);
v___x_1680_ = lean_nat_add(v___x_1580_, v_size_1673_);
lean_dec(v_size_1673_);
v___x_1681_ = lean_nat_add(v___x_1580_, v_size_1679_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 4, v_impl_1579_);
lean_ctor_set(v___x_1677_, 3, v_r_1672_);
lean_ctor_set(v___x_1677_, 2, v_v_1087_);
lean_ctor_set(v___x_1677_, 1, v_k_1086_);
lean_ctor_set(v___x_1677_, 0, v___x_1681_);
v___x_1683_ = v___x_1677_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_r_1672_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_impl_1579_);
v___x_1683_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v___x_1683_);
lean_ctor_set(v___x_1091_, 3, v_l_1671_);
lean_ctor_set(v___x_1091_, 2, v_v_1675_);
lean_ctor_set(v___x_1091_, 1, v_k_1674_);
lean_ctor_set(v___x_1091_, 0, v___x_1680_);
v___x_1685_ = v___x_1091_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_k_1674_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_v_1675_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_l_1671_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_k_1691_; lean_object* v_v_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1703_; 
v_k_1691_ = lean_ctor_get(v_l_1088_, 1);
v_v_1692_ = lean_ctor_get(v_l_1088_, 2);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_l_1088_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; lean_object* v_unused_1705_; lean_object* v_unused_1706_; 
v_unused_1704_ = lean_ctor_get(v_l_1088_, 4);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_l_1088_, 3);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_l_1088_, 0);
lean_dec(v_unused_1706_);
v___x_1694_ = v_l_1088_;
v_isShared_1695_ = v_isSharedCheck_1703_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_v_1692_);
lean_inc(v_k_1691_);
lean_dec(v_l_1088_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1703_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(3u);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 3, v_r_1672_);
lean_ctor_set(v___x_1694_, 2, v_v_1087_);
lean_ctor_set(v___x_1694_, 1, v_k_1086_);
lean_ctor_set(v___x_1694_, 0, v___x_1580_);
v___x_1698_ = v___x_1694_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v_r_1672_);
lean_ctor_set(v_reuseFailAlloc_1702_, 4, v_r_1672_);
v___x_1698_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1700_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v___x_1698_);
lean_ctor_set(v___x_1091_, 3, v_l_1671_);
lean_ctor_set(v___x_1091_, 2, v_v_1692_);
lean_ctor_set(v___x_1091_, 1, v_k_1691_);
lean_ctor_set(v___x_1091_, 0, v___x_1696_);
v___x_1700_ = v___x_1091_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_k_1691_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_v_1692_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_l_1671_);
lean_ctor_set(v_reuseFailAlloc_1701_, 4, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
else
{
lean_object* v_r_1707_; 
v_r_1707_ = lean_ctor_get(v_l_1088_, 4);
lean_inc(v_r_1707_);
if (lean_obj_tag(v_r_1707_) == 0)
{
lean_object* v_k_1708_; lean_object* v_v_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1732_; 
lean_inc(v_l_1671_);
v_k_1708_ = lean_ctor_get(v_l_1088_, 1);
v_v_1709_ = lean_ctor_get(v_l_1088_, 2);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_l_1088_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; lean_object* v_unused_1734_; lean_object* v_unused_1735_; 
v_unused_1733_ = lean_ctor_get(v_l_1088_, 4);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_l_1088_, 3);
lean_dec(v_unused_1734_);
v_unused_1735_ = lean_ctor_get(v_l_1088_, 0);
lean_dec(v_unused_1735_);
v___x_1711_ = v_l_1088_;
v_isShared_1712_ = v_isSharedCheck_1732_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_v_1709_);
lean_inc(v_k_1708_);
lean_dec(v_l_1088_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1732_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_k_1713_; lean_object* v_v_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1728_; 
v_k_1713_ = lean_ctor_get(v_r_1707_, 1);
v_v_1714_ = lean_ctor_get(v_r_1707_, 2);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_r_1707_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; lean_object* v_unused_1730_; lean_object* v_unused_1731_; 
v_unused_1729_ = lean_ctor_get(v_r_1707_, 4);
lean_dec(v_unused_1729_);
v_unused_1730_ = lean_ctor_get(v_r_1707_, 3);
lean_dec(v_unused_1730_);
v_unused_1731_ = lean_ctor_get(v_r_1707_, 0);
lean_dec(v_unused_1731_);
v___x_1716_ = v_r_1707_;
v_isShared_1717_ = v_isSharedCheck_1728_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_v_1714_);
lean_inc(v_k_1713_);
lean_dec(v_r_1707_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1728_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1718_ = lean_unsigned_to_nat(3u);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 4, v_l_1671_);
lean_ctor_set(v___x_1716_, 3, v_l_1671_);
lean_ctor_set(v___x_1716_, 2, v_v_1709_);
lean_ctor_set(v___x_1716_, 1, v_k_1708_);
lean_ctor_set(v___x_1716_, 0, v___x_1580_);
v___x_1720_ = v___x_1716_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_k_1708_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_v_1709_);
lean_ctor_set(v_reuseFailAlloc_1727_, 3, v_l_1671_);
lean_ctor_set(v_reuseFailAlloc_1727_, 4, v_l_1671_);
v___x_1720_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1722_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 4, v_l_1671_);
lean_ctor_set(v___x_1711_, 2, v_v_1087_);
lean_ctor_set(v___x_1711_, 1, v_k_1086_);
lean_ctor_set(v___x_1711_, 0, v___x_1580_);
v___x_1722_ = v___x_1711_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_l_1671_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v_l_1671_);
v___x_1722_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v___x_1722_);
lean_ctor_set(v___x_1091_, 3, v___x_1720_);
lean_ctor_set(v___x_1091_, 2, v_v_1714_);
lean_ctor_set(v___x_1091_, 1, v_k_1713_);
lean_ctor_set(v___x_1091_, 0, v___x_1718_);
v___x_1724_ = v___x_1091_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_k_1713_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_v_1714_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = lean_unsigned_to_nat(2u);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v_r_1707_);
lean_ctor_set(v___x_1091_, 0, v___x_1736_);
v___x_1738_ = v___x_1091_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1739_, 3, v_l_1088_);
lean_ctor_set(v_reuseFailAlloc_1739_, 4, v_r_1707_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v___x_1741_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v_l_1088_);
lean_ctor_set(v___x_1091_, 0, v___x_1580_);
v___x_1741_ = v___x_1091_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_l_1088_);
lean_ctor_set(v_reuseFailAlloc_1742_, 4, v_l_1088_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
}
else
{
return v_t_1085_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_1745_, lean_object* v_t_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1745_, v_t_1746_);
lean_dec(v_k_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_1748_, lean_object* v_declName_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; lean_object* v_ext_1754_; lean_object* v_toEnvExtension_1755_; lean_object* v_env_1756_; lean_object* v_asyncMode_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___y_1761_; lean_object* v_funCC_1787_; uint8_t v___x_1788_; 
v___x_1753_ = lean_st_ref_get(v_a_1751_);
v_ext_1754_ = lean_ctor_get(v_ext_1748_, 1);
v_toEnvExtension_1755_ = lean_ctor_get(v_ext_1754_, 0);
v_env_1756_ = lean_ctor_get(v___x_1753_, 0);
lean_inc_ref(v_env_1756_);
lean_dec(v___x_1753_);
v_asyncMode_1757_ = lean_ctor_get(v_toEnvExtension_1755_, 2);
v___x_1758_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1759_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1758_, v_ext_1748_, v_env_1756_, v_asyncMode_1757_);
v_funCC_1787_ = lean_ctor_get(v___x_1759_, 2);
lean_inc(v_funCC_1787_);
v___x_1788_ = l_Lean_NameSet_contains(v_funCC_1787_, v_declName_1749_);
lean_dec(v_funCC_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; 
lean_inc(v_declName_1749_);
v___x_1789_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_dec_ref_known(v___x_1789_, 1);
v___y_1761_ = v_a_1751_;
goto v___jp_1760_;
}
else
{
lean_dec(v___x_1759_);
lean_dec(v_declName_1749_);
lean_dec_ref(v_ext_1748_);
return v___x_1789_;
}
}
else
{
v___y_1761_ = v_a_1751_;
goto v___jp_1760_;
}
v___jp_1760_:
{
lean_object* v_funCC_1762_; lean_object* v___x_1763_; lean_object* v_env_1764_; lean_object* v_nextMacroScope_1765_; lean_object* v_ngen_1766_; lean_object* v_auxDeclNGen_1767_; lean_object* v_traceState_1768_; lean_object* v_messages_1769_; lean_object* v_infoState_1770_; lean_object* v_snapshotTasks_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1785_; 
v_funCC_1762_ = lean_ctor_get(v___x_1759_, 2);
lean_inc(v_funCC_1762_);
lean_dec(v___x_1759_);
v___x_1763_ = lean_st_ref_take(v___y_1761_);
v_env_1764_ = lean_ctor_get(v___x_1763_, 0);
v_nextMacroScope_1765_ = lean_ctor_get(v___x_1763_, 1);
v_ngen_1766_ = lean_ctor_get(v___x_1763_, 2);
v_auxDeclNGen_1767_ = lean_ctor_get(v___x_1763_, 3);
v_traceState_1768_ = lean_ctor_get(v___x_1763_, 4);
v_messages_1769_ = lean_ctor_get(v___x_1763_, 6);
v_infoState_1770_ = lean_ctor_get(v___x_1763_, 7);
v_snapshotTasks_1771_ = lean_ctor_get(v___x_1763_, 8);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v___x_1763_, 5);
lean_dec(v_unused_1786_);
v___x_1773_ = v___x_1763_;
v_isShared_1774_ = v_isSharedCheck_1785_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_snapshotTasks_1771_);
lean_inc(v_infoState_1770_);
lean_inc(v_messages_1769_);
lean_inc(v_traceState_1768_);
lean_inc(v_auxDeclNGen_1767_);
lean_inc(v_ngen_1766_);
lean_inc(v_nextMacroScope_1765_);
lean_inc(v_env_1764_);
lean_dec(v___x_1763_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1785_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___f_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1775_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_1749_, v_funCC_1762_);
lean_dec(v_declName_1749_);
v___f_1776_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_1776_, 0, v___x_1775_);
v___x_1777_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1748_, v_env_1764_, v___f_1776_);
v___x_1778_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 5, v___x_1778_);
lean_ctor_set(v___x_1773_, 0, v___x_1777_);
v___x_1780_ = v___x_1773_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_nextMacroScope_1765_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_ngen_1766_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v_auxDeclNGen_1767_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v_traceState_1768_);
lean_ctor_set(v_reuseFailAlloc_1784_, 5, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1784_, 6, v_messages_1769_);
lean_ctor_set(v_reuseFailAlloc_1784_, 7, v_infoState_1770_);
lean_ctor_set(v_reuseFailAlloc_1784_, 8, v_snapshotTasks_1771_);
v___x_1780_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_st_ref_set(v___y_1761_, v___x_1780_);
v___x_1782_ = lean_box(0);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_1790_, lean_object* v_declName_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1790_, v_declName_1791_, v_a_1792_, v_a_1793_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_1796_, lean_object* v_k_1797_, lean_object* v_t_1798_, lean_object* v_h_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1797_, v_t_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_1801_, lean_object* v_k_1802_, lean_object* v_t_1803_, lean_object* v_h_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_1801_, v_k_1802_, v_t_1803_, v_h_1804_);
lean_dec(v_k_1802_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_1806_, lean_object* v_s_1807_){
_start:
{
lean_object* v_casesTypes_1808_; lean_object* v_extThms_1809_; lean_object* v_funCC_1810_; lean_object* v_inj_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
v_casesTypes_1808_ = lean_ctor_get(v_s_1807_, 0);
v_extThms_1809_ = lean_ctor_get(v_s_1807_, 1);
v_funCC_1810_ = lean_ctor_get(v_s_1807_, 2);
v_inj_1811_ = lean_ctor_get(v_s_1807_, 4);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_s_1807_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v_s_1807_, 3);
lean_dec(v_unused_1819_);
v___x_1813_ = v_s_1807_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_inj_1811_);
lean_inc(v_funCC_1810_);
lean_inc(v_extThms_1809_);
lean_inc(v_casesTypes_1808_);
lean_dec(v_s_1807_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 3, v_a_1806_);
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_casesTypes_1808_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_extThms_1809_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_funCC_1810_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_a_1806_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_inj_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_1821_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
lean_ctor_set(v___x_1821_, 2, v___x_1820_);
lean_ctor_set(v___x_1821_, 3, v___x_1820_);
lean_ctor_set(v___x_1821_, 4, v___x_1820_);
lean_ctor_set(v___x_1821_, 5, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_1822_, lean_object* v_declName_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v___x_1829_; lean_object* v_ext_1830_; lean_object* v_toEnvExtension_1831_; lean_object* v_env_1832_; lean_object* v_asyncMode_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v_ematch_1836_; lean_object* v___x_1837_; 
v___x_1829_ = lean_st_ref_get(v_a_1827_);
v_ext_1830_ = lean_ctor_get(v_ext_1822_, 1);
v_toEnvExtension_1831_ = lean_ctor_get(v_ext_1830_, 0);
v_env_1832_ = lean_ctor_get(v___x_1829_, 0);
lean_inc_ref(v_env_1832_);
lean_dec(v___x_1829_);
v_asyncMode_1833_ = lean_ctor_get(v_toEnvExtension_1831_, 2);
v___x_1834_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1835_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1834_, v_ext_1822_, v_env_1832_, v_asyncMode_1833_);
v_ematch_1836_ = lean_ctor_get(v___x_1835_, 3);
lean_inc_ref(v_ematch_1836_);
lean_dec(v___x_1835_);
v___x_1837_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_1836_, v_declName_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1882_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1882_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1882_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v_env_1843_; lean_object* v_nextMacroScope_1844_; lean_object* v_ngen_1845_; lean_object* v_auxDeclNGen_1846_; lean_object* v_traceState_1847_; lean_object* v_messages_1848_; lean_object* v_infoState_1849_; lean_object* v_snapshotTasks_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1880_; 
v___x_1842_ = lean_st_ref_take(v_a_1827_);
v_env_1843_ = lean_ctor_get(v___x_1842_, 0);
v_nextMacroScope_1844_ = lean_ctor_get(v___x_1842_, 1);
v_ngen_1845_ = lean_ctor_get(v___x_1842_, 2);
v_auxDeclNGen_1846_ = lean_ctor_get(v___x_1842_, 3);
v_traceState_1847_ = lean_ctor_get(v___x_1842_, 4);
v_messages_1848_ = lean_ctor_get(v___x_1842_, 6);
v_infoState_1849_ = lean_ctor_get(v___x_1842_, 7);
v_snapshotTasks_1850_ = lean_ctor_get(v___x_1842_, 8);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v___x_1842_, 5);
lean_dec(v_unused_1881_);
v___x_1852_ = v___x_1842_;
v_isShared_1853_ = v_isSharedCheck_1880_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_snapshotTasks_1850_);
lean_inc(v_infoState_1849_);
lean_inc(v_messages_1848_);
lean_inc(v_traceState_1847_);
lean_inc(v_auxDeclNGen_1846_);
lean_inc(v_ngen_1845_);
lean_inc(v_nextMacroScope_1844_);
lean_inc(v_env_1843_);
lean_dec(v___x_1842_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1880_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___f_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___f_1854_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_1854_, 0, v_a_1838_);
v___x_1855_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1822_, v_env_1843_, v___f_1854_);
v___x_1856_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 5, v___x_1856_);
lean_ctor_set(v___x_1852_, 0, v___x_1855_);
v___x_1858_ = v___x_1852_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_nextMacroScope_1844_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_ngen_1845_);
lean_ctor_set(v_reuseFailAlloc_1879_, 3, v_auxDeclNGen_1846_);
lean_ctor_set(v_reuseFailAlloc_1879_, 4, v_traceState_1847_);
lean_ctor_set(v_reuseFailAlloc_1879_, 5, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1879_, 6, v_messages_1848_);
lean_ctor_set(v_reuseFailAlloc_1879_, 7, v_infoState_1849_);
lean_ctor_set(v_reuseFailAlloc_1879_, 8, v_snapshotTasks_1850_);
v___x_1858_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_mctx_1861_; lean_object* v_zetaDeltaFVarIds_1862_; lean_object* v_postponed_1863_; lean_object* v_diag_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1877_; 
v___x_1859_ = lean_st_ref_set(v_a_1827_, v___x_1858_);
v___x_1860_ = lean_st_ref_take(v_a_1825_);
v_mctx_1861_ = lean_ctor_get(v___x_1860_, 0);
v_zetaDeltaFVarIds_1862_ = lean_ctor_get(v___x_1860_, 2);
v_postponed_1863_ = lean_ctor_get(v___x_1860_, 3);
v_diag_1864_ = lean_ctor_get(v___x_1860_, 4);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1877_ == 0)
{
lean_object* v_unused_1878_; 
v_unused_1878_ = lean_ctor_get(v___x_1860_, 1);
lean_dec(v_unused_1878_);
v___x_1866_ = v___x_1860_;
v_isShared_1867_ = v_isSharedCheck_1877_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_diag_1864_);
lean_inc(v_postponed_1863_);
lean_inc(v_zetaDeltaFVarIds_1862_);
lean_inc(v_mctx_1861_);
lean_dec(v___x_1860_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1877_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1868_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 1, v___x_1868_);
v___x_1870_ = v___x_1866_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_mctx_1861_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1876_, 2, v_zetaDeltaFVarIds_1862_);
lean_ctor_set(v_reuseFailAlloc_1876_, 3, v_postponed_1863_);
lean_ctor_set(v_reuseFailAlloc_1876_, 4, v_diag_1864_);
v___x_1870_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1871_ = lean_st_ref_set(v_a_1825_, v___x_1870_);
v___x_1872_ = lean_box(0);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1872_);
v___x_1874_ = v___x_1840_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref(v_ext_1822_);
v_a_1883_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1837_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1837_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_1891_, lean_object* v_declName_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1891_, v_declName_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_1899_, lean_object* v_s_1900_){
_start:
{
lean_object* v_casesTypes_1901_; lean_object* v_extThms_1902_; lean_object* v_funCC_1903_; lean_object* v_ematch_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
v_casesTypes_1901_ = lean_ctor_get(v_s_1900_, 0);
v_extThms_1902_ = lean_ctor_get(v_s_1900_, 1);
v_funCC_1903_ = lean_ctor_get(v_s_1900_, 2);
v_ematch_1904_ = lean_ctor_get(v_s_1900_, 3);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_s_1900_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v_s_1900_, 4);
lean_dec(v_unused_1912_);
v___x_1906_ = v_s_1900_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_ematch_1904_);
lean_inc(v_funCC_1903_);
lean_inc(v_extThms_1902_);
lean_inc(v_casesTypes_1901_);
lean_dec(v_s_1900_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 4, v_a_1899_);
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_casesTypes_1901_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_extThms_1902_);
lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_funCC_1903_);
lean_ctor_set(v_reuseFailAlloc_1910_, 3, v_ematch_1904_);
lean_ctor_set(v_reuseFailAlloc_1910_, 4, v_a_1899_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_1913_, lean_object* v_declName_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; lean_object* v_ext_1921_; lean_object* v_toEnvExtension_1922_; lean_object* v_env_1923_; lean_object* v_asyncMode_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_inj_1927_; lean_object* v___x_1928_; 
v___x_1920_ = lean_st_ref_get(v_a_1918_);
v_ext_1921_ = lean_ctor_get(v_ext_1913_, 1);
v_toEnvExtension_1922_ = lean_ctor_get(v_ext_1921_, 0);
v_env_1923_ = lean_ctor_get(v___x_1920_, 0);
lean_inc_ref(v_env_1923_);
lean_dec(v___x_1920_);
v_asyncMode_1924_ = lean_ctor_get(v_toEnvExtension_1922_, 2);
v___x_1925_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1926_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1925_, v_ext_1913_, v_env_1923_, v_asyncMode_1924_);
v_inj_1927_ = lean_ctor_get(v___x_1926_, 4);
lean_inc_ref(v_inj_1927_);
lean_dec(v___x_1926_);
v___x_1928_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_1927_, v_declName_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1973_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1973_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1973_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v_env_1934_; lean_object* v_nextMacroScope_1935_; lean_object* v_ngen_1936_; lean_object* v_auxDeclNGen_1937_; lean_object* v_traceState_1938_; lean_object* v_messages_1939_; lean_object* v_infoState_1940_; lean_object* v_snapshotTasks_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1971_; 
v___x_1933_ = lean_st_ref_take(v_a_1918_);
v_env_1934_ = lean_ctor_get(v___x_1933_, 0);
v_nextMacroScope_1935_ = lean_ctor_get(v___x_1933_, 1);
v_ngen_1936_ = lean_ctor_get(v___x_1933_, 2);
v_auxDeclNGen_1937_ = lean_ctor_get(v___x_1933_, 3);
v_traceState_1938_ = lean_ctor_get(v___x_1933_, 4);
v_messages_1939_ = lean_ctor_get(v___x_1933_, 6);
v_infoState_1940_ = lean_ctor_get(v___x_1933_, 7);
v_snapshotTasks_1941_ = lean_ctor_get(v___x_1933_, 8);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; 
v_unused_1972_ = lean_ctor_get(v___x_1933_, 5);
lean_dec(v_unused_1972_);
v___x_1943_ = v___x_1933_;
v_isShared_1944_ = v_isSharedCheck_1971_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_snapshotTasks_1941_);
lean_inc(v_infoState_1940_);
lean_inc(v_messages_1939_);
lean_inc(v_traceState_1938_);
lean_inc(v_auxDeclNGen_1937_);
lean_inc(v_ngen_1936_);
lean_inc(v_nextMacroScope_1935_);
lean_inc(v_env_1934_);
lean_dec(v___x_1933_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1971_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___f_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___f_1945_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_1945_, 0, v_a_1929_);
v___x_1946_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1913_, v_env_1934_, v___f_1945_);
v___x_1947_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 5, v___x_1947_);
lean_ctor_set(v___x_1943_, 0, v___x_1946_);
v___x_1949_ = v___x_1943_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_nextMacroScope_1935_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_ngen_1936_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_auxDeclNGen_1937_);
lean_ctor_set(v_reuseFailAlloc_1970_, 4, v_traceState_1938_);
lean_ctor_set(v_reuseFailAlloc_1970_, 5, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1970_, 6, v_messages_1939_);
lean_ctor_set(v_reuseFailAlloc_1970_, 7, v_infoState_1940_);
lean_ctor_set(v_reuseFailAlloc_1970_, 8, v_snapshotTasks_1941_);
v___x_1949_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v_mctx_1952_; lean_object* v_zetaDeltaFVarIds_1953_; lean_object* v_postponed_1954_; lean_object* v_diag_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1968_; 
v___x_1950_ = lean_st_ref_set(v_a_1918_, v___x_1949_);
v___x_1951_ = lean_st_ref_take(v_a_1916_);
v_mctx_1952_ = lean_ctor_get(v___x_1951_, 0);
v_zetaDeltaFVarIds_1953_ = lean_ctor_get(v___x_1951_, 2);
v_postponed_1954_ = lean_ctor_get(v___x_1951_, 3);
v_diag_1955_ = lean_ctor_get(v___x_1951_, 4);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; 
v_unused_1969_ = lean_ctor_get(v___x_1951_, 1);
lean_dec(v_unused_1969_);
v___x_1957_ = v___x_1951_;
v_isShared_1958_ = v_isSharedCheck_1968_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_diag_1955_);
lean_inc(v_postponed_1954_);
lean_inc(v_zetaDeltaFVarIds_1953_);
lean_inc(v_mctx_1952_);
lean_dec(v___x_1951_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1968_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v___x_1959_);
v___x_1961_ = v___x_1957_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_mctx_1952_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_zetaDeltaFVarIds_1953_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_postponed_1954_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v_diag_1955_);
v___x_1961_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1962_ = lean_st_ref_set(v_a_1916_, v___x_1961_);
v___x_1963_ = lean_box(0);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1963_);
v___x_1965_ = v___x_1931_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v_ext_1913_);
v_a_1974_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1928_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1928_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_1982_, lean_object* v_declName_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_1982_, v_declName_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
return v_res_1989_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1990_, lean_object* v_i_1991_, lean_object* v_k_1992_){
_start:
{
lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = lean_array_get_size(v_keys_1990_);
v___x_1994_ = lean_nat_dec_lt(v_i_1991_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_dec(v_i_1991_);
return v___x_1994_;
}
else
{
lean_object* v_k_x27_1995_; uint8_t v___x_1996_; 
v_k_x27_1995_ = lean_array_fget_borrowed(v_keys_1990_, v_i_1991_);
v___x_1996_ = lean_name_eq(v_k_1992_, v_k_x27_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_unsigned_to_nat(1u);
v___x_1998_ = lean_nat_add(v_i_1991_, v___x_1997_);
lean_dec(v_i_1991_);
v_i_1991_ = v___x_1998_;
goto _start;
}
else
{
lean_dec(v_i_1991_);
return v___x_1996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2000_, lean_object* v_i_2001_, lean_object* v_k_2002_){
_start:
{
uint8_t v_res_2003_; lean_object* v_r_2004_; 
v_res_2003_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2000_, v_i_2001_, v_k_2002_);
lean_dec(v_k_2002_);
lean_dec_ref(v_keys_2000_);
v_r_2004_ = lean_box(v_res_2003_);
return v_r_2004_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_2005_, size_t v_x_2006_, lean_object* v_x_2007_){
_start:
{
if (lean_obj_tag(v_x_2005_) == 0)
{
lean_object* v_es_2008_; lean_object* v___x_2009_; size_t v___x_2010_; size_t v___x_2011_; lean_object* v_j_2012_; lean_object* v___x_2013_; 
v_es_2008_ = lean_ctor_get(v_x_2005_, 0);
v___x_2009_ = lean_box(2);
v___x_2010_ = ((size_t)31ULL);
v___x_2011_ = lean_usize_land(v_x_2006_, v___x_2010_);
v_j_2012_ = lean_usize_to_nat(v___x_2011_);
v___x_2013_ = lean_array_get_borrowed(v___x_2009_, v_es_2008_, v_j_2012_);
lean_dec(v_j_2012_);
switch(lean_obj_tag(v___x_2013_))
{
case 0:
{
lean_object* v_key_2014_; uint8_t v___x_2015_; 
v_key_2014_ = lean_ctor_get(v___x_2013_, 0);
v___x_2015_ = lean_name_eq(v_x_2007_, v_key_2014_);
return v___x_2015_;
}
case 1:
{
lean_object* v_node_2016_; size_t v___x_2017_; size_t v___x_2018_; 
v_node_2016_ = lean_ctor_get(v___x_2013_, 0);
v___x_2017_ = ((size_t)5ULL);
v___x_2018_ = lean_usize_shift_right(v_x_2006_, v___x_2017_);
v_x_2005_ = v_node_2016_;
v_x_2006_ = v___x_2018_;
goto _start;
}
default: 
{
uint8_t v___x_2020_; 
v___x_2020_ = 0;
return v___x_2020_;
}
}
}
else
{
lean_object* v_ks_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v_ks_2021_ = lean_ctor_get(v_x_2005_, 0);
v___x_2022_ = lean_unsigned_to_nat(0u);
v___x_2023_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_2021_, v___x_2022_, v_x_2007_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
size_t v_x_327__boxed_2027_; uint8_t v_res_2028_; lean_object* v_r_2029_; 
v_x_327__boxed_2027_ = lean_unbox_usize(v_x_2025_);
lean_dec(v_x_2025_);
v_res_2028_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2024_, v_x_327__boxed_2027_, v_x_2026_);
lean_dec(v_x_2026_);
lean_dec_ref(v_x_2024_);
v_r_2029_ = lean_box(v_res_2028_);
return v_r_2029_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2030_; uint64_t v___x_2031_; 
v___x_2030_ = lean_unsigned_to_nat(1723u);
v___x_2031_ = lean_uint64_of_nat(v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_2032_, lean_object* v_x_2033_){
_start:
{
uint64_t v___y_2035_; 
if (lean_obj_tag(v_x_2033_) == 0)
{
uint64_t v___x_2038_; 
v___x_2038_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_2035_ = v___x_2038_;
goto v___jp_2034_;
}
else
{
uint64_t v_hash_2039_; 
v_hash_2039_ = lean_ctor_get_uint64(v_x_2033_, sizeof(void*)*2);
v___y_2035_ = v_hash_2039_;
goto v___jp_2034_;
}
v___jp_2034_:
{
size_t v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = lean_uint64_to_usize(v___y_2035_);
v___x_2037_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2032_, v___x_2036_, v_x_2033_);
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_2040_, lean_object* v_x_2041_){
_start:
{
uint8_t v_res_2042_; lean_object* v_r_2043_; 
v_res_2042_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2040_, v_x_2041_);
lean_dec(v_x_2041_);
lean_dec_ref(v_x_2040_);
v_r_2043_ = lean_box(v_res_2042_);
return v_r_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_2044_, lean_object* v_declName_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v___x_2048_; lean_object* v_ext_2049_; lean_object* v_toEnvExtension_2050_; lean_object* v_env_2051_; lean_object* v_asyncMode_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v_extThms_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2048_ = lean_st_ref_get(v_a_2046_);
v_ext_2049_ = lean_ctor_get(v_ext_2044_, 1);
v_toEnvExtension_2050_ = lean_ctor_get(v_ext_2049_, 0);
v_env_2051_ = lean_ctor_get(v___x_2048_, 0);
lean_inc_ref(v_env_2051_);
lean_dec(v___x_2048_);
v_asyncMode_2052_ = lean_ctor_get(v_toEnvExtension_2050_, 2);
v___x_2053_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2054_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2053_, v_ext_2044_, v_env_2051_, v_asyncMode_2052_);
v_extThms_2055_ = lean_ctor_get(v___x_2054_, 1);
lean_inc_ref(v_extThms_2055_);
lean_dec(v___x_2054_);
v___x_2056_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_2055_, v_declName_2045_);
lean_dec_ref(v_extThms_2055_);
v___x_2057_ = lean_box(v___x_2056_);
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_2059_, lean_object* v_declName_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2059_, v_declName_2060_, v_a_2061_);
lean_dec(v_a_2061_);
lean_dec(v_declName_2060_);
lean_dec_ref(v_ext_2059_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_2064_, lean_object* v_declName_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2064_, v_declName_2065_, v_a_2067_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_2070_, lean_object* v_declName_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2070_, v_declName_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_declName_2071_);
lean_dec_ref(v_ext_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_2076_, lean_object* v_x_2077_, lean_object* v_x_2078_){
_start:
{
uint8_t v___x_2079_; 
v___x_2079_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2077_, v_x_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_2080_, lean_object* v_x_2081_, lean_object* v_x_2082_){
_start:
{
uint8_t v_res_2083_; lean_object* v_r_2084_; 
v_res_2083_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_2080_, v_x_2081_, v_x_2082_);
lean_dec(v_x_2082_);
lean_dec_ref(v_x_2081_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_2085_, lean_object* v_x_2086_, size_t v_x_2087_, lean_object* v_x_2088_){
_start:
{
uint8_t v___x_2089_; 
v___x_2089_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2086_, v_x_2087_, v_x_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_){
_start:
{
size_t v_x_418__boxed_2094_; uint8_t v_res_2095_; lean_object* v_r_2096_; 
v_x_418__boxed_2094_ = lean_unbox_usize(v_x_2092_);
lean_dec(v_x_2092_);
v_res_2095_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2090_, v_x_2091_, v_x_418__boxed_2094_, v_x_2093_);
lean_dec(v_x_2093_);
lean_dec_ref(v_x_2091_);
v_r_2096_ = lean_box(v_res_2095_);
return v_r_2096_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2097_, lean_object* v_keys_2098_, lean_object* v_vals_2099_, lean_object* v_heq_2100_, lean_object* v_i_2101_, lean_object* v_k_2102_){
_start:
{
uint8_t v___x_2103_; 
v___x_2103_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2098_, v_i_2101_, v_k_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2104_, lean_object* v_keys_2105_, lean_object* v_vals_2106_, lean_object* v_heq_2107_, lean_object* v_i_2108_, lean_object* v_k_2109_){
_start:
{
uint8_t v_res_2110_; lean_object* v_r_2111_; 
v_res_2110_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_2104_, v_keys_2105_, v_vals_2106_, v_heq_2107_, v_i_2108_, v_k_2109_);
lean_dec(v_k_2109_);
lean_dec_ref(v_vals_2106_);
lean_dec_ref(v_keys_2105_);
v_r_2111_ = lean_box(v_res_2110_);
return v_r_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_2112_, lean_object* v_declName_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v___x_2116_; lean_object* v_ext_2117_; lean_object* v_toEnvExtension_2118_; lean_object* v_env_2119_; lean_object* v_asyncMode_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v_inj_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2116_ = lean_st_ref_get(v_a_2114_);
v_ext_2117_ = lean_ctor_get(v_ext_2112_, 1);
v_toEnvExtension_2118_ = lean_ctor_get(v_ext_2117_, 0);
v_env_2119_ = lean_ctor_get(v___x_2116_, 0);
lean_inc_ref(v_env_2119_);
lean_dec(v___x_2116_);
v_asyncMode_2120_ = lean_ctor_get(v_toEnvExtension_2118_, 2);
v___x_2121_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2122_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2121_, v_ext_2112_, v_env_2119_, v_asyncMode_2120_);
v_inj_2123_ = lean_ctor_get(v___x_2122_, 4);
lean_inc_ref(v_inj_2123_);
lean_dec(v___x_2122_);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v_declName_2113_);
v___x_2125_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_2123_, v___x_2124_);
lean_dec_ref_known(v___x_2124_, 1);
lean_dec_ref(v_inj_2123_);
v___x_2126_ = lean_box(v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_2128_, lean_object* v_declName_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2128_, v_declName_2129_, v_a_2130_);
lean_dec(v_a_2130_);
lean_dec_ref(v_ext_2128_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_2133_, lean_object* v_declName_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2133_, v_declName_2134_, v_a_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_2139_, lean_object* v_declName_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2139_, v_declName_2140_, v_a_2141_, v_a_2142_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec_ref(v_ext_2139_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_2145_, lean_object* v_declName_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v___x_2149_; lean_object* v_ext_2150_; lean_object* v_toEnvExtension_2151_; lean_object* v_env_2152_; lean_object* v_asyncMode_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v_funCC_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2149_ = lean_st_ref_get(v_a_2147_);
v_ext_2150_ = lean_ctor_get(v_ext_2145_, 1);
v_toEnvExtension_2151_ = lean_ctor_get(v_ext_2150_, 0);
v_env_2152_ = lean_ctor_get(v___x_2149_, 0);
lean_inc_ref(v_env_2152_);
lean_dec(v___x_2149_);
v_asyncMode_2153_ = lean_ctor_get(v_toEnvExtension_2151_, 2);
v___x_2154_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2155_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2154_, v_ext_2145_, v_env_2152_, v_asyncMode_2153_);
v_funCC_2156_ = lean_ctor_get(v___x_2155_, 2);
lean_inc(v_funCC_2156_);
lean_dec(v___x_2155_);
v___x_2157_ = l_Lean_NameSet_contains(v_funCC_2156_, v_declName_2146_);
lean_dec(v_funCC_2156_);
v___x_2158_ = lean_box(v___x_2157_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_2160_, lean_object* v_declName_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2160_, v_declName_2161_, v_a_2162_);
lean_dec(v_a_2162_);
lean_dec(v_declName_2161_);
lean_dec_ref(v_ext_2160_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_2165_, lean_object* v_declName_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2165_, v_declName_2166_, v_a_2168_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_2171_, lean_object* v_declName_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2171_, v_declName_2172_, v_a_2173_, v_a_2174_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec(v_declName_2172_);
lean_dec_ref(v_ext_2171_);
return v_res_2176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_2201_ = l_Lean_mkAtom(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_2203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2204_ = lean_array_push(v___x_2203_, v___x_2202_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_2214_ = l_Lean_mkAtom(v___x_2213_);
return v___x_2214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_2216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2217_ = lean_array_push(v___x_2216_, v___x_2215_);
return v___x_2217_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2218_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_2219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_2220_ = lean_box(2);
v___x_2221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___x_2219_);
lean_ctor_set(v___x_2221_, 2, v___x_2218_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_2223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_2224_ = lean_array_push(v___x_2223_, v___x_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2225_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_2227_ = lean_box(2);
v___x_2228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v___x_2226_);
lean_ctor_set(v___x_2228_, 2, v___x_2225_);
return v___x_2228_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_2230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2231_ = lean_array_push(v___x_2230_, v___x_2229_);
return v___x_2231_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2232_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_2233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_2234_ = lean_box(2);
v___x_2235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v___x_2233_);
lean_ctor_set(v___x_2235_, 2, v___x_2232_);
return v___x_2235_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_2237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2238_ = lean_array_push(v___x_2237_, v___x_2236_);
return v___x_2238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2239_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_2240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_2241_ = lean_box(2);
v___x_2242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v___x_2240_);
lean_ctor_set(v___x_2242_, 2, v___x_2239_);
return v___x_2242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_2244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2245_ = lean_array_push(v___x_2244_, v___x_2243_);
return v___x_2245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_2247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_2248_ = lean_box(2);
v___x_2249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v___x_2247_);
lean_ctor_set(v___x_2249_, 2, v___x_2246_);
return v___x_2249_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_2251_, lean_object* v_ext_2252_, lean_object* v_____r_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = 0;
lean_inc(v_declName_2251_);
v___x_2260_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_2251_, v___x_2259_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; uint8_t v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2262_ = lean_unbox(v_a_2261_);
lean_dec(v_a_2261_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; lean_object* v_a_2264_; uint8_t v___x_2265_; 
v___x_2263_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2252_, v_declName_2251_, v___y_2257_);
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref(v___x_2263_);
v___x_2265_ = lean_unbox(v_a_2264_);
lean_dec(v_a_2264_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; lean_object* v_a_2267_; uint8_t v___x_2268_; 
lean_inc(v_declName_2251_);
v___x_2266_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2252_, v_declName_2251_, v___y_2257_);
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref(v___x_2266_);
v___x_2268_ = lean_unbox(v_a_2267_);
lean_dec(v_a_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v_a_2270_; uint8_t v___x_2271_; 
v___x_2269_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2252_, v_declName_2251_, v___y_2257_);
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref(v___x_2269_);
v___x_2271_ = lean_unbox(v_a_2270_);
lean_dec(v_a_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; 
v___x_2272_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_2252_, v_declName_2251_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; 
v___x_2273_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2252_, v_declName_2251_, v___y_2256_, v___y_2257_);
return v___x_2273_;
}
}
else
{
lean_object* v___x_2274_; 
v___x_2274_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_2252_, v_declName_2251_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2274_;
}
}
else
{
lean_object* v___x_2275_; 
v___x_2275_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2252_, v_declName_2251_, v___y_2256_, v___y_2257_);
return v___x_2275_;
}
}
else
{
lean_object* v___x_2276_; 
v___x_2276_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2252_, v_declName_2251_, v___y_2256_, v___y_2257_);
return v___x_2276_;
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v_ext_2252_);
lean_dec(v_declName_2251_);
v_a_2277_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2260_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2260_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_2285_, lean_object* v_ext_2286_, lean_object* v_____r_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2285_, v_ext_2286_, v_____r_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object* v_msgData_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; lean_object* v_env_2301_; lean_object* v___x_2302_; lean_object* v_mctx_2303_; lean_object* v_lctx_2304_; lean_object* v_options_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2300_ = lean_st_ref_get(v___y_2298_);
v_env_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc_ref(v_env_2301_);
lean_dec(v___x_2300_);
v___x_2302_ = lean_st_ref_get(v___y_2296_);
v_mctx_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc_ref(v_mctx_2303_);
lean_dec(v___x_2302_);
v_lctx_2304_ = lean_ctor_get(v___y_2295_, 2);
v_options_2305_ = lean_ctor_get(v___y_2297_, 2);
lean_inc_ref(v_options_2305_);
lean_inc_ref(v_lctx_2304_);
v___x_2306_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2306_, 0, v_env_2301_);
lean_ctor_set(v___x_2306_, 1, v_mctx_2303_);
lean_ctor_set(v___x_2306_, 2, v_lctx_2304_);
lean_ctor_set(v___x_2306_, 3, v_options_2305_);
v___x_2307_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v_msgData_2294_);
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object* v_msgData_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_ref_2322_; lean_object* v___x_2323_; lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2332_; 
v_ref_2322_ = lean_ctor_get(v___y_2319_, 5);
v___x_2323_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2332_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2332_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2330_; 
lean_inc(v_ref_2322_);
v___x_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2328_, 0, v_ref_2322_);
lean_ctor_set(v___x_2328_, 1, v_a_2324_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set_tag(v___x_2326_, 1);
lean_ctor_set(v___x_2326_, 0, v___x_2328_);
v___x_2330_ = v___x_2326_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
return v_res_2339_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2346_; uint64_t v___x_2347_; 
v___x_2346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2347_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2348_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2350_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set_uint64(v___x_2350_, sizeof(void*)*1, v___x_2348_);
return v___x_2350_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2351_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
return v___x_2353_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2354_ = lean_box(1);
v___x_2355_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set(v___x_2357_, 1, v___x_2355_);
lean_ctor_set(v___x_2357_, 2, v___x_2354_);
return v___x_2357_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
lean_ctor_set(v___x_2362_, 2, v___x_2361_);
lean_ctor_set(v___x_2362_, 3, v___x_2361_);
lean_ctor_set(v___x_2362_, 4, v___x_2360_);
lean_ctor_set(v___x_2362_, 5, v___x_2360_);
lean_ctor_set(v___x_2362_, 6, v___x_2360_);
lean_ctor_set(v___x_2362_, 7, v___x_2360_);
lean_ctor_set(v___x_2362_, 8, v___x_2360_);
lean_ctor_set(v___x_2362_, 9, v___x_2360_);
return v___x_2362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2364_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
lean_ctor_set(v___x_2364_, 2, v___x_2363_);
lean_ctor_set(v___x_2364_, 3, v___x_2363_);
lean_ctor_set(v___x_2364_, 4, v___x_2363_);
lean_ctor_set(v___x_2364_, 5, v___x_2363_);
return v___x_2364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
lean_ctor_set(v___x_2366_, 2, v___x_2365_);
lean_ctor_set(v___x_2366_, 3, v___x_2365_);
lean_ctor_set(v___x_2366_, 4, v___x_2365_);
return v___x_2366_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10));
v___x_2369_ = l_Lean_stringToMessageData(v___x_2368_);
return v___x_2369_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12));
v___x_2372_ = l_Lean_stringToMessageData(v___x_2371_);
return v___x_2372_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14));
v___x_2375_ = l_Lean_stringToMessageData(v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v___x_2376_, lean_object* v_ext_2377_, uint8_t v_showInfo_2378_, lean_object* v_attrName_2379_, lean_object* v_declName_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
uint8_t v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___y_2399_; 
v___x_2384_ = 1;
v___x_2385_ = 0;
v___x_2386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2387_ = lean_unsigned_to_nat(0u);
v___x_2388_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_2390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_2391_ = lean_box(0);
lean_inc(v___x_2376_);
v___x_2392_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2392_, 0, v___x_2386_);
lean_ctor_set(v___x_2392_, 1, v___x_2376_);
lean_ctor_set(v___x_2392_, 2, v___x_2389_);
lean_ctor_set(v___x_2392_, 3, v___x_2390_);
lean_ctor_set(v___x_2392_, 4, v___x_2391_);
lean_ctor_set(v___x_2392_, 5, v___x_2387_);
lean_ctor_set(v___x_2392_, 6, v___x_2391_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*7, v___x_2385_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*7 + 1, v___x_2385_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*7 + 2, v___x_2385_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*7 + 3, v___x_2384_);
v___x_2393_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_2394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2395_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_2396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2393_);
lean_ctor_set(v___x_2396_, 1, v___x_2394_);
lean_ctor_set(v___x_2396_, 2, v___x_2376_);
lean_ctor_set(v___x_2396_, 3, v___x_2388_);
lean_ctor_set(v___x_2396_, 4, v___x_2395_);
v___x_2397_ = lean_st_mk_ref(v___x_2396_);
if (v_showInfo_2378_ == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec(v_attrName_2379_);
v___x_2409_ = lean_box(0);
v___x_2410_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2380_, v_ext_2377_, v___x_2409_, v___x_2392_, v___x_2397_, v___y_2381_, v___y_2382_);
lean_dec_ref_known(v___x_2392_, 7);
v___y_2399_ = v___x_2410_;
goto v___jp_2398_;
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec(v_declName_2380_);
lean_dec_ref(v_ext_2377_);
v___x_2411_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11);
v___x_2412_ = l_Lean_MessageData_ofName(v_attrName_2379_);
lean_inc_ref(v___x_2412_);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13);
v___x_2415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v___x_2412_);
v___x_2417_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15);
v___x_2418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2418_, v___x_2392_, v___x_2397_, v___y_2381_, v___y_2382_);
lean_dec_ref_known(v___x_2392_, 7);
v___y_2399_ = v___x_2419_;
goto v___jp_2398_;
}
v___jp_2398_:
{
if (lean_obj_tag(v___y_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2408_; 
v_a_2400_ = lean_ctor_get(v___y_2399_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___y_2399_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2402_ = v___y_2399_;
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___y_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2404_ = lean_st_ref_get(v___x_2397_);
lean_dec(v___x_2397_);
lean_dec(v___x_2404_);
if (v_isShared_2403_ == 0)
{
v___x_2406_ = v___x_2402_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2400_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
else
{
lean_dec(v___x_2397_);
return v___y_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v___x_2420_, lean_object* v_ext_2421_, lean_object* v_showInfo_2422_, lean_object* v_attrName_2423_, lean_object* v_declName_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
uint8_t v_showInfo_boxed_2428_; lean_object* v_res_2429_; 
v_showInfo_boxed_2428_ = lean_unbox(v_showInfo_2422_);
v_res_2429_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v___x_2420_, v_ext_2421_, v_showInfo_boxed_2428_, v_attrName_2423_, v_declName_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2432_, uint8_t v_attrKind_2433_, uint8_t v_showInfo_2434_, uint8_t v_minIndexable_2435_, lean_object* v_as_x27_2436_, lean_object* v_b_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
if (lean_obj_tag(v_as_x27_2436_) == 0)
{
lean_object* v___x_2443_; 
lean_dec_ref(v_ext_2432_);
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v_b_2437_);
return v___x_2443_;
}
else
{
lean_object* v_head_2444_; lean_object* v_tail_2445_; lean_object* v___x_2446_; 
v_head_2444_ = lean_ctor_get(v_as_x27_2436_, 0);
v_tail_2445_ = lean_ctor_get(v_as_x27_2436_, 1);
v___x_2446_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2441_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2448_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_2444_);
lean_inc_ref(v_ext_2432_);
v___x_2449_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2432_, v_head_2444_, v_attrKind_2433_, v___x_2448_, v_a_2447_, v_showInfo_2434_, v_minIndexable_2435_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v___x_2450_; 
lean_dec_ref_known(v___x_2449_, 1);
v___x_2450_ = lean_box(0);
v_as_x27_2436_ = v_tail_2445_;
v_b_2437_ = v___x_2450_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2432_);
return v___x_2449_;
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec_ref(v_ext_2432_);
v_a_2452_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2446_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2446_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2460_, lean_object* v_attrKind_2461_, lean_object* v_showInfo_2462_, lean_object* v_minIndexable_2463_, lean_object* v_as_x27_2464_, lean_object* v_b_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
uint8_t v_attrKind_boxed_2471_; uint8_t v_showInfo_boxed_2472_; uint8_t v_minIndexable_boxed_2473_; lean_object* v_res_2474_; 
v_attrKind_boxed_2471_ = lean_unbox(v_attrKind_2461_);
v_showInfo_boxed_2472_ = lean_unbox(v_showInfo_2462_);
v_minIndexable_boxed_2473_ = lean_unbox(v_minIndexable_2463_);
v_res_2474_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2460_, v_attrKind_boxed_2471_, v_showInfo_boxed_2472_, v_minIndexable_boxed_2473_, v_as_x27_2464_, v_b_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v_as_x27_2464_);
return v_res_2474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2477_ = l_Lean_stringToMessageData(v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2480_ = l_Lean_stringToMessageData(v___x_2479_);
return v___x_2480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
return v___x_2483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_2486_ = l_Lean_stringToMessageData(v___x_2485_);
return v___x_2486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2492_ = l_Lean_stringToMessageData(v___x_2491_);
return v___x_2492_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12));
v___x_2495_ = l_Lean_stringToMessageData(v___x_2494_);
return v___x_2495_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14));
v___x_2498_ = l_Lean_stringToMessageData(v___x_2497_);
return v___x_2498_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16));
v___x_2501_ = l_Lean_stringToMessageData(v___x_2500_);
return v___x_2501_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18));
v___x_2504_ = l_Lean_stringToMessageData(v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_stx_2505_, lean_object* v_ext_2506_, lean_object* v_declName_2507_, uint8_t v_attrKind_2508_, uint8_t v_showInfo_2509_, uint8_t v_minIndexable_2510_, uint8_t v___x_2511_, lean_object* v_attrName_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2505_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
switch(lean_obj_tag(v_a_2547_))
{
case 0:
{
lean_object* v_k_2548_; 
lean_dec(v_attrName_2512_);
lean_dec(v_stx_2505_);
v_k_2548_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_k_2548_);
lean_dec_ref_known(v_a_2547_, 1);
if (lean_obj_tag(v_k_2548_) == 9)
{
lean_object* v___x_2549_; 
lean_dec(v_declName_2507_);
lean_dec_ref(v_ext_2506_);
v___x_2549_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2515_, v___y_2516_);
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2516_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
v___x_2552_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2506_, v_declName_2507_, v_attrKind_2508_, v_k_2548_, v_a_2551_, v_showInfo_2509_, v_minIndexable_2510_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2552_;
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_k_2548_);
lean_dec(v_declName_2507_);
lean_dec_ref(v_ext_2506_);
v_a_2553_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2550_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2550_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2561_; lean_object* v___x_2562_; 
lean_dec(v_attrName_2512_);
lean_dec(v_stx_2505_);
v_eager_2561_ = lean_ctor_get_uint8(v_a_2547_, 0);
lean_dec_ref_known(v_a_2547_, 0);
v___x_2562_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2506_, v_declName_2507_, v_eager_2561_, v_attrKind_2508_, v___y_2515_, v___y_2516_);
return v___x_2562_;
}
case 2:
{
lean_object* v___x_2563_; 
lean_dec(v_stx_2505_);
lean_inc(v_declName_2507_);
v___x_2563_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2507_, v___x_2511_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
if (lean_obj_tag(v_a_2564_) == 1)
{
lean_object* v_val_2565_; lean_object* v_ctors_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec(v_attrName_2512_);
lean_dec(v_declName_2507_);
v_val_2565_ = lean_ctor_get(v_a_2564_, 0);
lean_inc(v_val_2565_);
lean_dec_ref_known(v_a_2564_, 1);
v_ctors_2566_ = lean_ctor_get(v_val_2565_, 4);
lean_inc(v_ctors_2566_);
lean_dec(v_val_2565_);
v___x_2567_ = lean_box(0);
v___x_2568_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2506_, v_attrKind_2508_, v_showInfo_2509_, v_minIndexable_2510_, v_ctors_2566_, v___x_2567_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v_ctors_2566_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v___x_2568_, 0);
lean_dec(v_unused_2576_);
v___x_2570_ = v___x_2568_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_dec(v___x_2568_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2567_);
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2567_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
else
{
return v___x_2568_;
}
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_dec(v_a_2564_);
lean_dec_ref(v_ext_2506_);
v___x_2577_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_2578_ = l_Lean_MessageData_ofName(v_attrName_2512_);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = l_Lean_MessageData_ofConstName(v_declName_2507_, v___x_2511_);
v___x_2583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_2585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2583_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___x_2586_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2585_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2586_;
}
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec(v_attrName_2512_);
lean_dec(v_declName_2507_);
lean_dec_ref(v_ext_2506_);
v_a_2587_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2563_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2563_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
case 3:
{
lean_object* v___x_2595_; 
lean_dec(v_attrName_2512_);
lean_inc(v_declName_2507_);
v___x_2595_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2507_, v___x_2511_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
if (lean_obj_tag(v_a_2596_) == 1)
{
lean_object* v_val_2597_; lean_object* v___x_2598_; 
lean_dec(v_declName_2507_);
lean_dec(v_stx_2505_);
v_val_2597_ = lean_ctor_get(v_a_2596_, 0);
lean_inc_n(v_val_2597_, 2);
lean_dec_ref_known(v_a_2596_, 1);
lean_inc_ref(v_ext_2506_);
v___x_2598_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2506_, v_val_2597_, v___x_2511_, v_attrKind_2508_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v___x_2599_; 
lean_dec_ref_known(v___x_2598_, 1);
v___x_2599_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2597_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2620_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2620_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2620_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
if (lean_obj_tag(v_a_2600_) == 1)
{
lean_object* v_val_2604_; lean_object* v_ctors_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_del_object(v___x_2602_);
v_val_2604_ = lean_ctor_get(v_a_2600_, 0);
lean_inc(v_val_2604_);
lean_dec_ref_known(v_a_2600_, 1);
v_ctors_2605_ = lean_ctor_get(v_val_2604_, 4);
lean_inc(v_ctors_2605_);
lean_dec(v_val_2604_);
v___x_2606_ = lean_box(0);
v___x_2607_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2506_, v_attrKind_2508_, v_showInfo_2509_, v_minIndexable_2510_, v_ctors_2605_, v___x_2606_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v_ctors_2605_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v___x_2607_, 0);
lean_dec(v_unused_2615_);
v___x_2609_ = v___x_2607_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_dec(v___x_2607_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2606_);
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2606_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
else
{
return v___x_2607_;
}
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_dec(v_a_2600_);
lean_dec_ref(v_ext_2506_);
v___x_2616_ = lean_box(0);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2616_);
v___x_2618_ = v___x_2602_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v_ext_2506_);
v_a_2621_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2599_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2599_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_dec(v_val_2597_);
lean_dec_ref(v_ext_2506_);
return v___x_2598_;
}
}
else
{
lean_object* v___x_2629_; 
lean_dec(v_a_2596_);
v___x_2629_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2516_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2631_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2631_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2506_, v_stx_2505_, v_declName_2507_, v_attrKind_2508_, v_a_2630_, v_minIndexable_2510_, v_showInfo_2509_, v___x_2511_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2631_;
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_declName_2507_);
lean_dec_ref(v_ext_2506_);
lean_dec(v_stx_2505_);
v_a_2632_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2629_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2629_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec(v_declName_2507_);
lean_dec_ref(v_ext_2506_);
lean_dec(v_stx_2505_);
v_a_2640_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2595_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2595_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
case 4:
{
lean_object* v___x_2648_; 
lean_dec(v_attrName_2512_);
lean_dec(v_stx_2505_);
v___x_2648_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2506_, v_declName_2507_, v_attrKind_2508_, v___y_2515_, v___y_2516_);
return v___x_2648_;
}
case 5:
{
lean_object* v_prio_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
lean_dec_ref(v_ext_2506_);
lean_dec(v_stx_2505_);
v_prio_2649_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_prio_2649_);
lean_dec_ref_known(v_a_2547_, 1);
v___x_2650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2651_ = lean_name_eq(v_attrName_2512_, v___x_2650_);
lean_dec(v_attrName_2512_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_dec(v_prio_2649_);
lean_dec(v_declName_2507_);
v___x_2652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11);
v___x_2653_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2652_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2653_;
}
else
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2507_, v_attrKind_2508_, v_prio_2649_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2654_;
}
}
case 6:
{
lean_object* v___x_2655_; 
lean_dec(v_attrName_2512_);
lean_dec(v_stx_2505_);
v___x_2655_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2506_, v_declName_2507_, v_attrKind_2508_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2655_;
}
case 7:
{
lean_object* v___x_2656_; 
lean_dec(v_attrName_2512_);
lean_dec(v_stx_2505_);
v___x_2656_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2506_, v_declName_2507_, v_attrKind_2508_, v___y_2515_, v___y_2516_);
return v___x_2656_;
}
case 8:
{
uint8_t v_post_2657_; uint8_t v_inv_2658_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
lean_dec_ref(v_ext_2506_);
lean_dec(v_stx_2505_);
v_post_2657_ = lean_ctor_get_uint8(v_a_2547_, 0);
v_inv_2658_ = lean_ctor_get_uint8(v_a_2547_, 1);
lean_dec_ref_known(v_a_2547_, 0);
v___x_2667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2668_ = lean_name_eq(v_attrName_2512_, v___x_2667_);
lean_dec(v_attrName_2512_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
lean_dec(v_declName_2507_);
v___x_2669_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13);
v___x_2670_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2669_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2670_;
}
else
{
v___y_2660_ = v___y_2513_;
v___y_2661_ = v___y_2514_;
v___y_2662_ = v___y_2515_;
v___y_2663_ = v___y_2516_;
goto v___jp_2659_;
}
v___jp_2659_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = l_Lean_Meta_Grind_normExt;
v___x_2665_ = lean_unsigned_to_nat(1000u);
v___x_2666_ = l_Lean_Meta_addSimpTheorem(v___x_2664_, v_declName_2507_, v_post_2657_, v_inv_2658_, v_attrKind_2508_, v___x_2665_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
return v___x_2666_;
}
}
case 9:
{
lean_object* v___x_2671_; uint8_t v___x_2672_; 
lean_dec_ref(v_ext_2506_);
lean_dec(v_stx_2505_);
v___x_2671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2672_ = lean_name_eq(v_attrName_2512_, v___x_2671_);
lean_dec(v_attrName_2512_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec(v_declName_2507_);
v___x_2673_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15);
v___x_2674_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2673_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2674_;
}
else
{
v___y_2519_ = v___y_2513_;
v___y_2520_ = v___y_2514_;
v___y_2521_ = v___y_2515_;
v___y_2522_ = v___y_2516_;
goto v___jp_2518_;
}
}
case 10:
{
lean_object* v___x_2675_; uint8_t v___x_2676_; 
lean_dec_ref(v_ext_2506_);
lean_dec(v_stx_2505_);
v___x_2675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2676_ = lean_name_eq(v_attrName_2512_, v___x_2675_);
lean_dec(v_attrName_2512_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec(v_declName_2507_);
v___x_2677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17);
v___x_2678_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2677_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_2507_, v_attrKind_2508_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2679_;
}
}
default: 
{
lean_object* v___x_2680_; uint8_t v___x_2681_; 
lean_dec_ref(v_ext_2506_);
lean_dec(v_stx_2505_);
v___x_2680_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2681_ = lean_name_eq(v_attrName_2512_, v___x_2680_);
lean_dec(v_attrName_2512_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
lean_dec(v_declName_2507_);
v___x_2682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19);
v___x_2683_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2682_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2683_;
}
else
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_2507_, v_attrKind_2508_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2684_;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_attrName_2512_);
lean_dec(v_declName_2507_);
lean_dec_ref(v_ext_2506_);
lean_dec(v_stx_2505_);
v_a_2685_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2546_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2546_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
v___jp_2518_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = l_Lean_Meta_Grind_normExt;
v___x_2524_ = lean_unsigned_to_nat(1000u);
v___x_2525_ = l_Lean_Meta_addDeclToUnfold(v___x_2523_, v_declName_2507_, v___x_2511_, v___x_2511_, v___x_2524_, v_attrKind_2508_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2537_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2537_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2537_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
uint8_t v___x_2530_; 
v___x_2530_ = lean_unbox(v_a_2526_);
lean_dec(v_a_2526_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_del_object(v___x_2528_);
v___x_2531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2532_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2531_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
return v___x_2532_;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2533_ = lean_box(0);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2533_);
v___x_2535_ = v___x_2528_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_a_2538_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2525_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2525_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_stx_2693_, lean_object* v_ext_2694_, lean_object* v_declName_2695_, lean_object* v_attrKind_2696_, lean_object* v_showInfo_2697_, lean_object* v_minIndexable_2698_, lean_object* v___x_2699_, lean_object* v_attrName_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
uint8_t v_attrKind_boxed_2706_; uint8_t v_showInfo_boxed_2707_; uint8_t v_minIndexable_boxed_2708_; uint8_t v___x_15810__boxed_2709_; lean_object* v_res_2710_; 
v_attrKind_boxed_2706_ = lean_unbox(v_attrKind_2696_);
v_showInfo_boxed_2707_ = lean_unbox(v_showInfo_2697_);
v_minIndexable_boxed_2708_ = lean_unbox(v_minIndexable_2698_);
v___x_15810__boxed_2709_ = lean_unbox(v___x_2699_);
v_res_2710_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_stx_2693_, v_ext_2694_, v_declName_2695_, v_attrKind_boxed_2706_, v_showInfo_boxed_2707_, v_minIndexable_boxed_2708_, v___x_15810__boxed_2709_, v_attrName_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
return v_res_2710_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2711_; double v___x_2712_; 
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = lean_float_of_nat(v___x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_2716_, lean_object* v_msg_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_ref_2723_; lean_object* v___x_2724_; lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2769_; 
v_ref_2723_ = lean_ctor_get(v___y_2720_, 5);
v___x_2724_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2727_ = v___x_2724_;
v_isShared_2728_ = v_isSharedCheck_2769_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2724_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2769_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v_traceState_2730_; lean_object* v_env_2731_; lean_object* v_nextMacroScope_2732_; lean_object* v_ngen_2733_; lean_object* v_auxDeclNGen_2734_; lean_object* v_cache_2735_; lean_object* v_messages_2736_; lean_object* v_infoState_2737_; lean_object* v_snapshotTasks_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2768_; 
v___x_2729_ = lean_st_ref_take(v___y_2721_);
v_traceState_2730_ = lean_ctor_get(v___x_2729_, 4);
v_env_2731_ = lean_ctor_get(v___x_2729_, 0);
v_nextMacroScope_2732_ = lean_ctor_get(v___x_2729_, 1);
v_ngen_2733_ = lean_ctor_get(v___x_2729_, 2);
v_auxDeclNGen_2734_ = lean_ctor_get(v___x_2729_, 3);
v_cache_2735_ = lean_ctor_get(v___x_2729_, 5);
v_messages_2736_ = lean_ctor_get(v___x_2729_, 6);
v_infoState_2737_ = lean_ctor_get(v___x_2729_, 7);
v_snapshotTasks_2738_ = lean_ctor_get(v___x_2729_, 8);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2740_ = v___x_2729_;
v_isShared_2741_ = v_isSharedCheck_2768_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_snapshotTasks_2738_);
lean_inc(v_infoState_2737_);
lean_inc(v_messages_2736_);
lean_inc(v_cache_2735_);
lean_inc(v_traceState_2730_);
lean_inc(v_auxDeclNGen_2734_);
lean_inc(v_ngen_2733_);
lean_inc(v_nextMacroScope_2732_);
lean_inc(v_env_2731_);
lean_dec(v___x_2729_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2768_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
uint64_t v_tid_2742_; lean_object* v_traces_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2767_; 
v_tid_2742_ = lean_ctor_get_uint64(v_traceState_2730_, sizeof(void*)*1);
v_traces_2743_ = lean_ctor_get(v_traceState_2730_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_traceState_2730_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2745_ = v_traceState_2730_;
v_isShared_2746_ = v_isSharedCheck_2767_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_traces_2743_);
lean_dec(v_traceState_2730_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2767_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; double v___x_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2747_ = lean_box(0);
v___x_2748_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_2749_ = 0;
v___x_2750_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2751_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2751_, 0, v_cls_2716_);
lean_ctor_set(v___x_2751_, 1, v___x_2747_);
lean_ctor_set(v___x_2751_, 2, v___x_2750_);
lean_ctor_set_float(v___x_2751_, sizeof(void*)*3, v___x_2748_);
lean_ctor_set_float(v___x_2751_, sizeof(void*)*3 + 8, v___x_2748_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*3 + 16, v___x_2749_);
v___x_2752_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_2753_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v_a_2725_);
lean_ctor_set(v___x_2753_, 2, v___x_2752_);
lean_inc(v_ref_2723_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_ref_2723_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Lean_PersistentArray_push___redArg(v_traces_2743_, v___x_2754_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2755_);
v___x_2757_ = v___x_2745_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2755_);
lean_ctor_set_uint64(v_reuseFailAlloc_2766_, sizeof(void*)*1, v_tid_2742_);
v___x_2757_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2759_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 4, v___x_2757_);
v___x_2759_ = v___x_2740_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_env_2731_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_nextMacroScope_2732_);
lean_ctor_set(v_reuseFailAlloc_2765_, 2, v_ngen_2733_);
lean_ctor_set(v_reuseFailAlloc_2765_, 3, v_auxDeclNGen_2734_);
lean_ctor_set(v_reuseFailAlloc_2765_, 4, v___x_2757_);
lean_ctor_set(v_reuseFailAlloc_2765_, 5, v_cache_2735_);
lean_ctor_set(v_reuseFailAlloc_2765_, 6, v_messages_2736_);
lean_ctor_set(v_reuseFailAlloc_2765_, 7, v_infoState_2737_);
lean_ctor_set(v_reuseFailAlloc_2765_, 8, v_snapshotTasks_2738_);
v___x_2759_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2760_ = lean_st_ref_set(v___y_2721_, v___x_2759_);
v___x_2761_ = lean_box(0);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2761_);
v___x_2763_ = v___x_2727_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_2770_, lean_object* v_msg_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2770_, v_msg_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2777_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_2778_, lean_object* v_i_2779_, lean_object* v_k_2780_){
_start:
{
lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2781_ = lean_array_get_size(v_keys_2778_);
v___x_2782_ = lean_nat_dec_lt(v_i_2779_, v___x_2781_);
if (v___x_2782_ == 0)
{
lean_dec(v_i_2779_);
return v___x_2782_;
}
else
{
lean_object* v_k_x27_2783_; uint8_t v___x_2784_; 
v_k_x27_2783_ = lean_array_fget_borrowed(v_keys_2778_, v_i_2779_);
v___x_2784_ = l_Lean_instBEqExtraModUse_beq(v_k_2780_, v_k_x27_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = lean_unsigned_to_nat(1u);
v___x_2786_ = lean_nat_add(v_i_2779_, v___x_2785_);
lean_dec(v_i_2779_);
v_i_2779_ = v___x_2786_;
goto _start;
}
else
{
lean_dec(v_i_2779_);
return v___x_2784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_2788_, lean_object* v_i_2789_, lean_object* v_k_2790_){
_start:
{
uint8_t v_res_2791_; lean_object* v_r_2792_; 
v_res_2791_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2788_, v_i_2789_, v_k_2790_);
lean_dec_ref(v_k_2790_);
lean_dec_ref(v_keys_2788_);
v_r_2792_ = lean_box(v_res_2791_);
return v_r_2792_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2793_, size_t v_x_2794_, lean_object* v_x_2795_){
_start:
{
if (lean_obj_tag(v_x_2793_) == 0)
{
lean_object* v_es_2796_; lean_object* v___x_2797_; size_t v___x_2798_; size_t v___x_2799_; lean_object* v_j_2800_; lean_object* v___x_2801_; 
v_es_2796_ = lean_ctor_get(v_x_2793_, 0);
v___x_2797_ = lean_box(2);
v___x_2798_ = ((size_t)31ULL);
v___x_2799_ = lean_usize_land(v_x_2794_, v___x_2798_);
v_j_2800_ = lean_usize_to_nat(v___x_2799_);
v___x_2801_ = lean_array_get_borrowed(v___x_2797_, v_es_2796_, v_j_2800_);
lean_dec(v_j_2800_);
switch(lean_obj_tag(v___x_2801_))
{
case 0:
{
lean_object* v_key_2802_; uint8_t v___x_2803_; 
v_key_2802_ = lean_ctor_get(v___x_2801_, 0);
v___x_2803_ = l_Lean_instBEqExtraModUse_beq(v_x_2795_, v_key_2802_);
return v___x_2803_;
}
case 1:
{
lean_object* v_node_2804_; size_t v___x_2805_; size_t v___x_2806_; 
v_node_2804_ = lean_ctor_get(v___x_2801_, 0);
v___x_2805_ = ((size_t)5ULL);
v___x_2806_ = lean_usize_shift_right(v_x_2794_, v___x_2805_);
v_x_2793_ = v_node_2804_;
v_x_2794_ = v___x_2806_;
goto _start;
}
default: 
{
uint8_t v___x_2808_; 
v___x_2808_ = 0;
return v___x_2808_;
}
}
}
else
{
lean_object* v_ks_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_ks_2809_ = lean_ctor_get(v_x_2793_, 0);
v___x_2810_ = lean_unsigned_to_nat(0u);
v___x_2811_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_ks_2809_, v___x_2810_, v_x_2795_);
return v___x_2811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2812_, lean_object* v_x_2813_, lean_object* v_x_2814_){
_start:
{
size_t v_x_16334__boxed_2815_; uint8_t v_res_2816_; lean_object* v_r_2817_; 
v_x_16334__boxed_2815_ = lean_unbox_usize(v_x_2813_);
lean_dec(v_x_2813_);
v_res_2816_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2812_, v_x_16334__boxed_2815_, v_x_2814_);
lean_dec_ref(v_x_2814_);
lean_dec_ref(v_x_2812_);
v_r_2817_ = lean_box(v_res_2816_);
return v_r_2817_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2818_, lean_object* v_x_2819_){
_start:
{
uint64_t v___x_2820_; size_t v___x_2821_; uint8_t v___x_2822_; 
v___x_2820_ = l_Lean_instHashableExtraModUse_hash(v_x_2819_);
v___x_2821_ = lean_uint64_to_usize(v___x_2820_);
v___x_2822_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2818_, v___x_2821_, v_x_2819_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2823_, lean_object* v_x_2824_){
_start:
{
uint8_t v_res_2825_; lean_object* v_r_2826_; 
v_res_2825_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2823_, v_x_2824_);
lean_dec_ref(v_x_2824_);
lean_dec_ref(v_x_2823_);
v_r_2826_ = lean_box(v_res_2825_);
return v_r_2826_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2829_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1));
v___x_2830_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0));
v___x_2831_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2830_, v___x_2829_);
return v___x_2831_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2837_ = l_Lean_stringToMessageData(v___x_2836_);
return v___x_2837_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7));
v___x_2840_ = l_Lean_stringToMessageData(v___x_2839_);
return v___x_2840_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2842_ = l_Lean_stringToMessageData(v___x_2841_);
return v___x_2842_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_cls_2846_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2847_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11));
v___x_2848_ = l_Lean_Name_append(v___x_2847_, v_cls_2846_);
return v___x_2848_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13));
v___x_2851_ = l_Lean_stringToMessageData(v___x_2850_);
return v___x_2851_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___x_2854_ = l_Lean_stringToMessageData(v___x_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2859_, uint8_t v_isMeta_2860_, lean_object* v_hint_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v___x_2867_; lean_object* v_env_2868_; uint8_t v_isExporting_2869_; lean_object* v___x_2870_; lean_object* v_env_2871_; lean_object* v___x_2872_; lean_object* v_entry_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2867_ = lean_st_ref_get(v___y_2865_);
v_env_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc_ref(v_env_2868_);
lean_dec(v___x_2867_);
v_isExporting_2869_ = lean_ctor_get_uint8(v_env_2868_, sizeof(void*)*8);
lean_dec_ref(v_env_2868_);
v___x_2870_ = lean_st_ref_get(v___y_2865_);
v_env_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc_ref(v_env_2871_);
lean_dec(v___x_2870_);
v___x_2872_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_2859_);
v_entry_2873_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2873_, 0, v_mod_2859_);
lean_ctor_set_uint8(v_entry_2873_, sizeof(void*)*1, v_isExporting_2869_);
lean_ctor_set_uint8(v_entry_2873_, sizeof(void*)*1 + 1, v_isMeta_2860_);
v___x_2874_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2875_ = lean_box(1);
v___x_2876_ = lean_box(0);
v___x_2919_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2872_, v___x_2874_, v_env_2871_, v___x_2875_, v___x_2876_);
v___x_2920_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2919_, v_entry_2873_);
lean_dec(v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v_options_2921_; uint8_t v_hasTrace_2922_; 
v_options_2921_ = lean_ctor_get(v___y_2864_, 2);
v_hasTrace_2922_ = lean_ctor_get_uint8(v_options_2921_, sizeof(void*)*1);
if (v_hasTrace_2922_ == 0)
{
lean_dec(v_hint_2861_);
lean_dec(v_mod_2859_);
v___y_2878_ = v___y_2863_;
v___y_2879_ = v___y_2865_;
goto v___jp_2877_;
}
else
{
lean_object* v_inheritedTraceOptions_2923_; lean_object* v_cls_2924_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___x_2944_; uint8_t v___x_2945_; 
v_inheritedTraceOptions_2923_ = lean_ctor_get(v___y_2864_, 13);
v_cls_2924_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2944_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_2945_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2923_, v_options_2921_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_dec(v_hint_2861_);
lean_dec(v_mod_2859_);
v___y_2878_ = v___y_2863_;
v___y_2879_ = v___y_2865_;
goto v___jp_2877_;
}
else
{
lean_object* v___x_2946_; lean_object* v___y_2948_; 
v___x_2946_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_2869_ == 0)
{
lean_object* v___x_2955_; 
v___x_2955_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_2948_ = v___x_2955_;
goto v___jp_2947_;
}
else
{
lean_object* v___x_2956_; 
v___x_2956_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_2948_ = v___x_2956_;
goto v___jp_2947_;
}
v___jp_2947_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
lean_inc_ref(v___y_2948_);
v___x_2949_ = l_Lean_stringToMessageData(v___y_2948_);
v___x_2950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2946_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_2952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2950_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
if (v_isMeta_2860_ == 0)
{
lean_object* v___x_2953_; 
v___x_2953_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_2931_ = v___x_2952_;
v___y_2932_ = v___x_2953_;
goto v___jp_2930_;
}
else
{
lean_object* v___x_2954_; 
v___x_2954_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_2931_ = v___x_2952_;
v___y_2932_ = v___x_2954_;
goto v___jp_2930_;
}
}
}
v___jp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___y_2926_);
lean_ctor_set(v___x_2928_, 1, v___y_2927_);
v___x_2929_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2924_, v___x_2928_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_dec_ref_known(v___x_2929_, 1);
v___y_2878_ = v___y_2863_;
v___y_2879_ = v___y_2865_;
goto v___jp_2877_;
}
else
{
lean_dec_ref_known(v_entry_2873_, 1);
return v___x_2929_;
}
}
v___jp_2930_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
lean_inc_ref(v___y_2932_);
v___x_2933_ = l_Lean_stringToMessageData(v___y_2932_);
v___x_2934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___y_2931_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_2936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2934_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
v___x_2937_ = l_Lean_MessageData_ofName(v_mod_2859_);
v___x_2938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = l_Lean_Name_isAnonymous(v_hint_2861_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_2941_ = l_Lean_MessageData_ofName(v_hint_2861_);
v___x_2942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___y_2926_ = v___x_2938_;
v___y_2927_ = v___x_2942_;
goto v___jp_2925_;
}
else
{
lean_object* v___x_2943_; 
lean_dec(v_hint_2861_);
v___x_2943_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_2926_ = v___x_2938_;
v___y_2927_ = v___x_2943_;
goto v___jp_2925_;
}
}
}
}
else
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
lean_dec_ref_known(v_entry_2873_, 1);
lean_dec(v_hint_2861_);
lean_dec(v_mod_2859_);
v___x_2957_ = lean_box(0);
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
return v___x_2958_;
}
v___jp_2877_:
{
lean_object* v___x_2880_; lean_object* v_toEnvExtension_2881_; lean_object* v_env_2882_; lean_object* v_nextMacroScope_2883_; lean_object* v_ngen_2884_; lean_object* v_auxDeclNGen_2885_; lean_object* v_traceState_2886_; lean_object* v_messages_2887_; lean_object* v_infoState_2888_; lean_object* v_snapshotTasks_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2917_; 
v___x_2880_ = lean_st_ref_take(v___y_2879_);
v_toEnvExtension_2881_ = lean_ctor_get(v___x_2874_, 0);
v_env_2882_ = lean_ctor_get(v___x_2880_, 0);
v_nextMacroScope_2883_ = lean_ctor_get(v___x_2880_, 1);
v_ngen_2884_ = lean_ctor_get(v___x_2880_, 2);
v_auxDeclNGen_2885_ = lean_ctor_get(v___x_2880_, 3);
v_traceState_2886_ = lean_ctor_get(v___x_2880_, 4);
v_messages_2887_ = lean_ctor_get(v___x_2880_, 6);
v_infoState_2888_ = lean_ctor_get(v___x_2880_, 7);
v_snapshotTasks_2889_ = lean_ctor_get(v___x_2880_, 8);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2917_ == 0)
{
lean_object* v_unused_2918_; 
v_unused_2918_ = lean_ctor_get(v___x_2880_, 5);
lean_dec(v_unused_2918_);
v___x_2891_ = v___x_2880_;
v_isShared_2892_ = v_isSharedCheck_2917_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_snapshotTasks_2889_);
lean_inc(v_infoState_2888_);
lean_inc(v_messages_2887_);
lean_inc(v_traceState_2886_);
lean_inc(v_auxDeclNGen_2885_);
lean_inc(v_ngen_2884_);
lean_inc(v_nextMacroScope_2883_);
lean_inc(v_env_2882_);
lean_dec(v___x_2880_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2917_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v_asyncMode_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v_asyncMode_2893_ = lean_ctor_get(v_toEnvExtension_2881_, 2);
v___x_2894_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2874_, v_env_2882_, v_entry_2873_, v_asyncMode_2893_, v___x_2876_);
v___x_2895_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 5, v___x_2895_);
lean_ctor_set(v___x_2891_, 0, v___x_2894_);
v___x_2897_ = v___x_2891_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_nextMacroScope_2883_);
lean_ctor_set(v_reuseFailAlloc_2916_, 2, v_ngen_2884_);
lean_ctor_set(v_reuseFailAlloc_2916_, 3, v_auxDeclNGen_2885_);
lean_ctor_set(v_reuseFailAlloc_2916_, 4, v_traceState_2886_);
lean_ctor_set(v_reuseFailAlloc_2916_, 5, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2916_, 6, v_messages_2887_);
lean_ctor_set(v_reuseFailAlloc_2916_, 7, v_infoState_2888_);
lean_ctor_set(v_reuseFailAlloc_2916_, 8, v_snapshotTasks_2889_);
v___x_2897_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v_mctx_2900_; lean_object* v_zetaDeltaFVarIds_2901_; lean_object* v_postponed_2902_; lean_object* v_diag_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2914_; 
v___x_2898_ = lean_st_ref_set(v___y_2879_, v___x_2897_);
v___x_2899_ = lean_st_ref_take(v___y_2878_);
v_mctx_2900_ = lean_ctor_get(v___x_2899_, 0);
v_zetaDeltaFVarIds_2901_ = lean_ctor_get(v___x_2899_, 2);
v_postponed_2902_ = lean_ctor_get(v___x_2899_, 3);
v_diag_2903_ = lean_ctor_get(v___x_2899_, 4);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; 
v_unused_2915_ = lean_ctor_get(v___x_2899_, 1);
lean_dec(v_unused_2915_);
v___x_2905_ = v___x_2899_;
v_isShared_2906_ = v_isSharedCheck_2914_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_diag_2903_);
lean_inc(v_postponed_2902_);
lean_inc(v_zetaDeltaFVarIds_2901_);
lean_inc(v_mctx_2900_);
lean_dec(v___x_2899_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2914_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 1, v___x_2907_);
v___x_2909_ = v___x_2905_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_mctx_2900_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_zetaDeltaFVarIds_2901_);
lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_postponed_2902_);
lean_ctor_set(v_reuseFailAlloc_2913_, 4, v_diag_2903_);
v___x_2909_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = lean_st_ref_set(v___y_2878_, v___x_2909_);
v___x_2911_ = lean_box(0);
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
return v___x_2912_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_2959_, lean_object* v_isMeta_2960_, lean_object* v_hint_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
uint8_t v_isMeta_boxed_2967_; lean_object* v_res_2968_; 
v_isMeta_boxed_2967_ = lean_unbox(v_isMeta_2960_);
v_res_2968_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2959_, v_isMeta_boxed_2967_, v_hint_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object* v_a_2969_, lean_object* v_x_2970_){
_start:
{
if (lean_obj_tag(v_x_2970_) == 0)
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_box(0);
return v___x_2971_;
}
else
{
lean_object* v_key_2972_; lean_object* v_value_2973_; lean_object* v_tail_2974_; uint8_t v___x_2975_; 
v_key_2972_ = lean_ctor_get(v_x_2970_, 0);
v_value_2973_ = lean_ctor_get(v_x_2970_, 1);
v_tail_2974_ = lean_ctor_get(v_x_2970_, 2);
v___x_2975_ = lean_name_eq(v_key_2972_, v_a_2969_);
if (v___x_2975_ == 0)
{
v_x_2970_ = v_tail_2974_;
goto _start;
}
else
{
lean_object* v___x_2977_; 
lean_inc(v_value_2973_);
v___x_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2977_, 0, v_value_2973_);
return v___x_2977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_a_2978_, lean_object* v_x_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2978_, v_x_2979_);
lean_dec(v_x_2979_);
lean_dec(v_a_2978_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_buckets_2983_; lean_object* v___x_2984_; uint64_t v___y_2986_; 
v_buckets_2983_ = lean_ctor_get(v_m_2981_, 1);
v___x_2984_ = lean_array_get_size(v_buckets_2983_);
if (lean_obj_tag(v_a_2982_) == 0)
{
uint64_t v___x_3000_; 
v___x_3000_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_2986_ = v___x_3000_;
goto v___jp_2985_;
}
else
{
uint64_t v_hash_3001_; 
v_hash_3001_ = lean_ctor_get_uint64(v_a_2982_, sizeof(void*)*2);
v___y_2986_ = v_hash_3001_;
goto v___jp_2985_;
}
v___jp_2985_:
{
uint64_t v___x_2987_; uint64_t v___x_2988_; uint64_t v_fold_2989_; uint64_t v___x_2990_; uint64_t v___x_2991_; uint64_t v___x_2992_; size_t v___x_2993_; size_t v___x_2994_; size_t v___x_2995_; size_t v___x_2996_; size_t v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2987_ = 32ULL;
v___x_2988_ = lean_uint64_shift_right(v___y_2986_, v___x_2987_);
v_fold_2989_ = lean_uint64_xor(v___y_2986_, v___x_2988_);
v___x_2990_ = 16ULL;
v___x_2991_ = lean_uint64_shift_right(v_fold_2989_, v___x_2990_);
v___x_2992_ = lean_uint64_xor(v_fold_2989_, v___x_2991_);
v___x_2993_ = lean_uint64_to_usize(v___x_2992_);
v___x_2994_ = lean_usize_of_nat(v___x_2984_);
v___x_2995_ = ((size_t)1ULL);
v___x_2996_ = lean_usize_sub(v___x_2994_, v___x_2995_);
v___x_2997_ = lean_usize_land(v___x_2993_, v___x_2996_);
v___x_2998_ = lean_array_uget_borrowed(v_buckets_2983_, v___x_2997_);
v___x_2999_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2982_, v___x_2998_);
return v___x_2999_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3002_, v_a_3003_);
lean_dec(v_a_3003_);
lean_dec_ref(v_m_3002_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_3005_, lean_object* v_declName_3006_, lean_object* v_as_3007_, size_t v_sz_3008_, size_t v_i_3009_, lean_object* v_b_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_usize_dec_lt(v_i_3009_, v_sz_3008_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; 
lean_dec(v_declName_3006_);
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_b_3010_);
return v___x_3017_;
}
else
{
lean_object* v___x_3018_; lean_object* v_modules_3019_; lean_object* v___x_3020_; lean_object* v_a_3021_; lean_object* v___x_3022_; lean_object* v_toImport_3023_; lean_object* v_module_3024_; uint8_t v___x_3025_; lean_object* v___x_3026_; 
v___x_3018_ = l_Lean_Environment_header(v___x_3005_);
v_modules_3019_ = lean_ctor_get(v___x_3018_, 3);
lean_inc_ref(v_modules_3019_);
lean_dec_ref(v___x_3018_);
v___x_3020_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3021_ = lean_array_uget_borrowed(v_as_3007_, v_i_3009_);
v___x_3022_ = lean_array_get(v___x_3020_, v_modules_3019_, v_a_3021_);
lean_dec_ref(v_modules_3019_);
v_toImport_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc_ref(v_toImport_3023_);
lean_dec(v___x_3022_);
v_module_3024_ = lean_ctor_get(v_toImport_3023_, 0);
lean_inc(v_module_3024_);
lean_dec_ref(v_toImport_3023_);
v___x_3025_ = 0;
lean_inc(v_declName_3006_);
v___x_3026_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3024_, v___x_3025_, v_declName_3006_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v___x_3027_; size_t v___x_3028_; size_t v___x_3029_; 
lean_dec_ref_known(v___x_3026_, 1);
v___x_3027_ = lean_box(0);
v___x_3028_ = ((size_t)1ULL);
v___x_3029_ = lean_usize_add(v_i_3009_, v___x_3028_);
v_i_3009_ = v___x_3029_;
v_b_3010_ = v___x_3027_;
goto _start;
}
else
{
lean_dec(v_declName_3006_);
return v___x_3026_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_3031_, lean_object* v_declName_3032_, lean_object* v_as_3033_, lean_object* v_sz_3034_, lean_object* v_i_3035_, lean_object* v_b_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
size_t v_sz_boxed_3042_; size_t v_i_boxed_3043_; lean_object* v_res_3044_; 
v_sz_boxed_3042_ = lean_unbox_usize(v_sz_3034_);
lean_dec(v_sz_3034_);
v_i_boxed_3043_ = lean_unbox_usize(v_i_3035_);
lean_dec(v_i_3035_);
v_res_3044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_3031_, v_declName_3032_, v_as_3033_, v_sz_boxed_3042_, v_i_boxed_3043_, v_b_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec_ref(v_as_3033_);
lean_dec_ref(v___x_3031_);
return v_res_3044_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___x_3048_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0));
v___x_3049_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3048_, v___x_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_3052_, uint8_t v_isMeta_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v___x_3059_; lean_object* v_env_3063_; lean_object* v___y_3065_; lean_object* v___x_3078_; 
v___x_3059_ = lean_st_ref_get(v___y_3057_);
v_env_3063_ = lean_ctor_get(v___x_3059_, 0);
lean_inc_ref(v_env_3063_);
lean_dec(v___x_3059_);
v___x_3078_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3063_, v_declName_3052_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_dec_ref(v_env_3063_);
lean_dec(v_declName_3052_);
goto v___jp_3060_;
}
else
{
lean_object* v_val_3079_; lean_object* v___x_3080_; lean_object* v_modules_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
v_val_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_val_3079_);
lean_dec_ref_known(v___x_3078_, 1);
v___x_3080_ = l_Lean_Environment_header(v_env_3063_);
v_modules_3081_ = lean_ctor_get(v___x_3080_, 3);
lean_inc_ref(v_modules_3081_);
lean_dec_ref(v___x_3080_);
v___x_3082_ = lean_array_get_size(v_modules_3081_);
v___x_3083_ = lean_nat_dec_lt(v_val_3079_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_dec_ref(v_modules_3081_);
lean_dec(v_val_3079_);
lean_dec_ref(v_env_3063_);
lean_dec(v_declName_3052_);
goto v___jp_3060_;
}
else
{
lean_object* v___x_3084_; lean_object* v_env_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; uint8_t v___y_3089_; 
v___x_3084_ = lean_st_ref_get(v___y_3057_);
v_env_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc_ref(v_env_3085_);
lean_dec(v___x_3084_);
v___x_3086_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3087_ = lean_array_fget(v_modules_3081_, v_val_3079_);
lean_dec(v_val_3079_);
lean_dec_ref(v_modules_3081_);
if (v_isMeta_3053_ == 0)
{
lean_dec_ref(v_env_3085_);
v___y_3089_ = v_isMeta_3053_;
goto v___jp_3088_;
}
else
{
uint8_t v___x_3100_; 
lean_inc(v_declName_3052_);
v___x_3100_ = l_Lean_isMarkedMeta(v_env_3085_, v_declName_3052_);
if (v___x_3100_ == 0)
{
v___y_3089_ = v_isMeta_3053_;
goto v___jp_3088_;
}
else
{
uint8_t v___x_3101_; 
v___x_3101_ = 0;
v___y_3089_ = v___x_3101_;
goto v___jp_3088_;
}
}
v___jp_3088_:
{
lean_object* v_toImport_3090_; lean_object* v_module_3091_; lean_object* v___x_3092_; 
v_toImport_3090_ = lean_ctor_get(v___x_3087_, 0);
lean_inc_ref(v_toImport_3090_);
lean_dec(v___x_3087_);
v_module_3091_ = lean_ctor_get(v_toImport_3090_, 0);
lean_inc(v_module_3091_);
lean_dec_ref(v_toImport_3090_);
lean_inc(v_declName_3052_);
v___x_3092_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3091_, v___y_3089_, v_declName_3052_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
lean_dec_ref_known(v___x_3092_, 1);
v___x_3093_ = l_Lean_indirectModUseExt;
v___x_3094_ = lean_box(1);
v___x_3095_ = lean_box(0);
lean_inc_ref(v_env_3063_);
v___x_3096_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3086_, v___x_3093_, v_env_3063_, v___x_3094_, v___x_3095_);
v___x_3097_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3096_, v_declName_3052_);
lean_dec(v___x_3096_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v___x_3098_; 
v___x_3098_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3065_ = v___x_3098_;
goto v___jp_3064_;
}
else
{
lean_object* v_val_3099_; 
v_val_3099_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_val_3099_);
lean_dec_ref_known(v___x_3097_, 1);
v___y_3065_ = v_val_3099_;
goto v___jp_3064_;
}
}
else
{
lean_dec_ref(v_env_3063_);
lean_dec(v_declName_3052_);
return v___x_3092_;
}
}
}
}
v___jp_3060_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_box(0);
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
return v___x_3062_;
}
v___jp_3064_:
{
lean_object* v___x_3066_; size_t v_sz_3067_; size_t v___x_3068_; lean_object* v___x_3069_; 
v___x_3066_ = lean_box(0);
v_sz_3067_ = lean_array_size(v___y_3065_);
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_3063_, v_declName_3052_, v___y_3065_, v_sz_3067_, v___x_3068_, v___x_3066_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec_ref(v___y_3065_);
lean_dec_ref(v_env_3063_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v___x_3069_, 0);
lean_dec(v_unused_3077_);
v___x_3071_ = v___x_3069_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_dec(v___x_3069_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 0, v___x_3066_);
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3066_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
else
{
return v___x_3069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3102_, lean_object* v_isMeta_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
uint8_t v_isMeta_boxed_3109_; lean_object* v_res_3110_; 
v_isMeta_boxed_3109_ = lean_unbox(v_isMeta_3103_);
v_res_3110_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3102_, v_isMeta_boxed_3109_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3111_, uint8_t v_isExporting_3112_, lean_object* v___x_3113_, lean_object* v___y_3114_, lean_object* v___x_3115_, lean_object* v_a_x3f_3116_){
_start:
{
lean_object* v___x_3118_; lean_object* v_env_3119_; lean_object* v_nextMacroScope_3120_; lean_object* v_ngen_3121_; lean_object* v_auxDeclNGen_3122_; lean_object* v_traceState_3123_; lean_object* v_messages_3124_; lean_object* v_infoState_3125_; lean_object* v_snapshotTasks_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3151_; 
v___x_3118_ = lean_st_ref_take(v___y_3111_);
v_env_3119_ = lean_ctor_get(v___x_3118_, 0);
v_nextMacroScope_3120_ = lean_ctor_get(v___x_3118_, 1);
v_ngen_3121_ = lean_ctor_get(v___x_3118_, 2);
v_auxDeclNGen_3122_ = lean_ctor_get(v___x_3118_, 3);
v_traceState_3123_ = lean_ctor_get(v___x_3118_, 4);
v_messages_3124_ = lean_ctor_get(v___x_3118_, 6);
v_infoState_3125_ = lean_ctor_get(v___x_3118_, 7);
v_snapshotTasks_3126_ = lean_ctor_get(v___x_3118_, 8);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v___x_3118_, 5);
lean_dec(v_unused_3152_);
v___x_3128_ = v___x_3118_;
v_isShared_3129_ = v_isSharedCheck_3151_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_snapshotTasks_3126_);
lean_inc(v_infoState_3125_);
lean_inc(v_messages_3124_);
lean_inc(v_traceState_3123_);
lean_inc(v_auxDeclNGen_3122_);
lean_inc(v_ngen_3121_);
lean_inc(v_nextMacroScope_3120_);
lean_inc(v_env_3119_);
lean_dec(v___x_3118_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3151_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3130_ = l_Lean_Environment_setExporting(v_env_3119_, v_isExporting_3112_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 5, v___x_3113_);
lean_ctor_set(v___x_3128_, 0, v___x_3130_);
v___x_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_nextMacroScope_3120_);
lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_ngen_3121_);
lean_ctor_set(v_reuseFailAlloc_3150_, 3, v_auxDeclNGen_3122_);
lean_ctor_set(v_reuseFailAlloc_3150_, 4, v_traceState_3123_);
lean_ctor_set(v_reuseFailAlloc_3150_, 5, v___x_3113_);
lean_ctor_set(v_reuseFailAlloc_3150_, 6, v_messages_3124_);
lean_ctor_set(v_reuseFailAlloc_3150_, 7, v_infoState_3125_);
lean_ctor_set(v_reuseFailAlloc_3150_, 8, v_snapshotTasks_3126_);
v___x_3132_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v_mctx_3135_; lean_object* v_zetaDeltaFVarIds_3136_; lean_object* v_postponed_3137_; lean_object* v_diag_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3148_; 
v___x_3133_ = lean_st_ref_set(v___y_3111_, v___x_3132_);
v___x_3134_ = lean_st_ref_take(v___y_3114_);
v_mctx_3135_ = lean_ctor_get(v___x_3134_, 0);
v_zetaDeltaFVarIds_3136_ = lean_ctor_get(v___x_3134_, 2);
v_postponed_3137_ = lean_ctor_get(v___x_3134_, 3);
v_diag_3138_ = lean_ctor_get(v___x_3134_, 4);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; 
v_unused_3149_ = lean_ctor_get(v___x_3134_, 1);
lean_dec(v_unused_3149_);
v___x_3140_ = v___x_3134_;
v_isShared_3141_ = v_isSharedCheck_3148_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_diag_3138_);
lean_inc(v_postponed_3137_);
lean_inc(v_zetaDeltaFVarIds_3136_);
lean_inc(v_mctx_3135_);
lean_dec(v___x_3134_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3148_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 1, v___x_3115_);
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_mctx_3135_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_zetaDeltaFVarIds_3136_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v_postponed_3137_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v_diag_3138_);
v___x_3143_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = lean_st_ref_set(v___y_3114_, v___x_3143_);
v___x_3145_ = lean_box(0);
v___x_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
return v___x_3146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3153_, lean_object* v_isExporting_3154_, lean_object* v___x_3155_, lean_object* v___y_3156_, lean_object* v___x_3157_, lean_object* v_a_x3f_3158_, lean_object* v___y_3159_){
_start:
{
uint8_t v_isExporting_boxed_3160_; lean_object* v_res_3161_; 
v_isExporting_boxed_3160_ = lean_unbox(v_isExporting_3154_);
v_res_3161_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3153_, v_isExporting_boxed_3160_, v___x_3155_, v___y_3156_, v___x_3157_, v_a_x3f_3158_);
lean_dec(v_a_x3f_3158_);
lean_dec(v___y_3156_);
lean_dec(v___y_3153_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3162_, uint8_t v_isExporting_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; lean_object* v_env_3170_; uint8_t v_isExporting_3171_; lean_object* v___x_3237_; uint8_t v_isModule_3238_; 
v___x_3169_ = lean_st_ref_get(v___y_3167_);
v_env_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc_ref(v_env_3170_);
lean_dec(v___x_3169_);
v_isExporting_3171_ = lean_ctor_get_uint8(v_env_3170_, sizeof(void*)*8);
v___x_3237_ = l_Lean_Environment_header(v_env_3170_);
lean_dec_ref(v_env_3170_);
v_isModule_3238_ = lean_ctor_get_uint8(v___x_3237_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3237_);
if (v_isModule_3238_ == 0)
{
lean_object* v___x_3239_; 
lean_inc(v___y_3167_);
lean_inc_ref(v___y_3166_);
lean_inc(v___y_3165_);
lean_inc_ref(v___y_3164_);
v___x_3239_ = lean_apply_5(v_x_3162_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, lean_box(0));
return v___x_3239_;
}
else
{
if (v_isExporting_3171_ == 0)
{
if (v_isExporting_3163_ == 0)
{
lean_object* v___x_3240_; 
lean_inc(v___y_3167_);
lean_inc_ref(v___y_3166_);
lean_inc(v___y_3165_);
lean_inc_ref(v___y_3164_);
v___x_3240_ = lean_apply_5(v_x_3162_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, lean_box(0));
return v___x_3240_;
}
else
{
goto v___jp_3172_;
}
}
else
{
if (v_isExporting_3163_ == 0)
{
goto v___jp_3172_;
}
else
{
lean_object* v___x_3241_; 
lean_inc(v___y_3167_);
lean_inc_ref(v___y_3166_);
lean_inc(v___y_3165_);
lean_inc_ref(v___y_3164_);
v___x_3241_ = lean_apply_5(v_x_3162_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, lean_box(0));
return v___x_3241_;
}
}
}
v___jp_3172_:
{
lean_object* v___x_3173_; lean_object* v_env_3174_; lean_object* v_nextMacroScope_3175_; lean_object* v_ngen_3176_; lean_object* v_auxDeclNGen_3177_; lean_object* v_traceState_3178_; lean_object* v_messages_3179_; lean_object* v_infoState_3180_; lean_object* v_snapshotTasks_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3235_; 
v___x_3173_ = lean_st_ref_take(v___y_3167_);
v_env_3174_ = lean_ctor_get(v___x_3173_, 0);
v_nextMacroScope_3175_ = lean_ctor_get(v___x_3173_, 1);
v_ngen_3176_ = lean_ctor_get(v___x_3173_, 2);
v_auxDeclNGen_3177_ = lean_ctor_get(v___x_3173_, 3);
v_traceState_3178_ = lean_ctor_get(v___x_3173_, 4);
v_messages_3179_ = lean_ctor_get(v___x_3173_, 6);
v_infoState_3180_ = lean_ctor_get(v___x_3173_, 7);
v_snapshotTasks_3181_ = lean_ctor_get(v___x_3173_, 8);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3235_ == 0)
{
lean_object* v_unused_3236_; 
v_unused_3236_ = lean_ctor_get(v___x_3173_, 5);
lean_dec(v_unused_3236_);
v___x_3183_ = v___x_3173_;
v_isShared_3184_ = v_isSharedCheck_3235_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_snapshotTasks_3181_);
lean_inc(v_infoState_3180_);
lean_inc(v_messages_3179_);
lean_inc(v_traceState_3178_);
lean_inc(v_auxDeclNGen_3177_);
lean_inc(v_ngen_3176_);
lean_inc(v_nextMacroScope_3175_);
lean_inc(v_env_3174_);
lean_dec(v___x_3173_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3235_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3188_; 
v___x_3185_ = l_Lean_Environment_setExporting(v_env_3174_, v_isExporting_3163_);
v___x_3186_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 5, v___x_3186_);
lean_ctor_set(v___x_3183_, 0, v___x_3185_);
v___x_3188_ = v___x_3183_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3185_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v_nextMacroScope_3175_);
lean_ctor_set(v_reuseFailAlloc_3234_, 2, v_ngen_3176_);
lean_ctor_set(v_reuseFailAlloc_3234_, 3, v_auxDeclNGen_3177_);
lean_ctor_set(v_reuseFailAlloc_3234_, 4, v_traceState_3178_);
lean_ctor_set(v_reuseFailAlloc_3234_, 5, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3234_, 6, v_messages_3179_);
lean_ctor_set(v_reuseFailAlloc_3234_, 7, v_infoState_3180_);
lean_ctor_set(v_reuseFailAlloc_3234_, 8, v_snapshotTasks_3181_);
v___x_3188_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v_mctx_3191_; lean_object* v_zetaDeltaFVarIds_3192_; lean_object* v_postponed_3193_; lean_object* v_diag_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3232_; 
v___x_3189_ = lean_st_ref_set(v___y_3167_, v___x_3188_);
v___x_3190_ = lean_st_ref_take(v___y_3165_);
v_mctx_3191_ = lean_ctor_get(v___x_3190_, 0);
v_zetaDeltaFVarIds_3192_ = lean_ctor_get(v___x_3190_, 2);
v_postponed_3193_ = lean_ctor_get(v___x_3190_, 3);
v_diag_3194_ = lean_ctor_get(v___x_3190_, 4);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; 
v_unused_3233_ = lean_ctor_get(v___x_3190_, 1);
lean_dec(v_unused_3233_);
v___x_3196_ = v___x_3190_;
v_isShared_3197_ = v_isSharedCheck_3232_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_diag_3194_);
lean_inc(v_postponed_3193_);
lean_inc(v_zetaDeltaFVarIds_3192_);
lean_inc(v_mctx_3191_);
lean_dec(v___x_3190_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3232_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 1, v___x_3198_);
v___x_3200_ = v___x_3196_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_mctx_3191_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_zetaDeltaFVarIds_3192_);
lean_ctor_set(v_reuseFailAlloc_3231_, 3, v_postponed_3193_);
lean_ctor_set(v_reuseFailAlloc_3231_, 4, v_diag_3194_);
v___x_3200_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3201_; lean_object* v_r_3202_; 
v___x_3201_ = lean_st_ref_set(v___y_3165_, v___x_3200_);
lean_inc(v___y_3167_);
lean_inc_ref(v___y_3166_);
lean_inc(v___y_3165_);
lean_inc_ref(v___y_3164_);
v_r_3202_ = lean_apply_5(v_x_3162_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, lean_box(0));
if (lean_obj_tag(v_r_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3219_; 
v_a_3203_ = lean_ctor_get(v_r_3202_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_r_3202_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3205_ = v_r_3202_;
v_isShared_3206_ = v_isSharedCheck_3219_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v_r_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3219_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
lean_inc(v_a_3203_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set_tag(v___x_3205_, 1);
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
v___x_3209_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3167_, v_isExporting_3171_, v___x_3186_, v___y_3165_, v___x_3198_, v___x_3208_);
lean_dec_ref(v___x_3208_);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; 
v_unused_3217_ = lean_ctor_get(v___x_3209_, 0);
lean_dec(v_unused_3217_);
v___x_3211_ = v___x_3209_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_dec(v___x_3209_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v_a_3203_);
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3203_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
v_a_3220_ = lean_ctor_get(v_r_3202_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v_r_3202_, 1);
v___x_3221_ = lean_box(0);
v___x_3222_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3167_, v_isExporting_3171_, v___x_3186_, v___y_3165_, v___x_3198_, v___x_3221_);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v___x_3222_, 0);
lean_dec(v_unused_3230_);
v___x_3224_ = v___x_3222_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_dec(v___x_3222_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set_tag(v___x_3224_, 1);
lean_ctor_set(v___x_3224_, 0, v_a_3220_);
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3220_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3242_, lean_object* v_isExporting_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
uint8_t v_isExporting_boxed_3249_; lean_object* v_res_3250_; 
v_isExporting_boxed_3249_ = lean_unbox(v_isExporting_3243_);
v_res_3250_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3242_, v_isExporting_boxed_3249_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3251_, uint8_t v_when_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
if (v_when_3252_ == 0)
{
lean_object* v___x_3258_; 
lean_inc(v___y_3256_);
lean_inc_ref(v___y_3255_);
lean_inc(v___y_3254_);
lean_inc_ref(v___y_3253_);
v___x_3258_ = lean_apply_5(v_x_3251_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, lean_box(0));
return v___x_3258_;
}
else
{
uint8_t v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = 0;
v___x_3260_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3251_, v___x_3259_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
return v___x_3260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3261_, lean_object* v_when_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
uint8_t v_when_boxed_3268_; lean_object* v_res_3269_; 
v_when_boxed_3268_ = lean_unbox(v_when_3262_);
v_res_3269_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3261_, v_when_boxed_3268_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v___x_3270_, lean_object* v_ext_3271_, uint8_t v_showInfo_3272_, uint8_t v_minIndexable_3273_, lean_object* v_attrName_3274_, lean_object* v_declName_3275_, lean_object* v_stx_3276_, uint8_t v_attrKind_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
uint8_t v___x_3281_; uint8_t v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___y_3298_; lean_object* v___x_3308_; 
v___x_3281_ = 0;
v___x_3282_ = 1;
v___x_3283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3284_ = lean_unsigned_to_nat(32u);
v___x_3285_ = lean_mk_empty_array_with_capacity(v___x_3284_);
lean_dec_ref(v___x_3285_);
v___x_3286_ = lean_unsigned_to_nat(0u);
v___x_3287_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3288_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_3289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_3290_ = lean_box(0);
lean_inc(v___x_3270_);
v___x_3291_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3291_, 0, v___x_3283_);
lean_ctor_set(v___x_3291_, 1, v___x_3270_);
lean_ctor_set(v___x_3291_, 2, v___x_3288_);
lean_ctor_set(v___x_3291_, 3, v___x_3289_);
lean_ctor_set(v___x_3291_, 4, v___x_3290_);
lean_ctor_set(v___x_3291_, 5, v___x_3286_);
lean_ctor_set(v___x_3291_, 6, v___x_3290_);
lean_ctor_set_uint8(v___x_3291_, sizeof(void*)*7, v___x_3281_);
lean_ctor_set_uint8(v___x_3291_, sizeof(void*)*7 + 1, v___x_3281_);
lean_ctor_set_uint8(v___x_3291_, sizeof(void*)*7 + 2, v___x_3281_);
lean_ctor_set_uint8(v___x_3291_, sizeof(void*)*7 + 3, v___x_3282_);
v___x_3292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3293_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3294_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_3295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3292_);
lean_ctor_set(v___x_3295_, 1, v___x_3293_);
lean_ctor_set(v___x_3295_, 2, v___x_3270_);
lean_ctor_set(v___x_3295_, 3, v___x_3287_);
lean_ctor_set(v___x_3295_, 4, v___x_3294_);
v___x_3296_ = lean_st_mk_ref(v___x_3295_);
lean_inc(v_declName_3275_);
v___x_3308_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3275_, v___x_3281_, v___x_3291_, v___x_3296_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___f_3313_; lean_object* v___x_3314_; 
lean_dec_ref_known(v___x_3308_, 1);
v___x_3309_ = lean_box(v_attrKind_3277_);
v___x_3310_ = lean_box(v_showInfo_3272_);
v___x_3311_ = lean_box(v_minIndexable_3273_);
v___x_3312_ = lean_box(v___x_3281_);
v___f_3313_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3313_, 0, v_stx_3276_);
lean_closure_set(v___f_3313_, 1, v_ext_3271_);
lean_closure_set(v___f_3313_, 2, v_declName_3275_);
lean_closure_set(v___f_3313_, 3, v___x_3309_);
lean_closure_set(v___f_3313_, 4, v___x_3310_);
lean_closure_set(v___f_3313_, 5, v___x_3311_);
lean_closure_set(v___f_3313_, 6, v___x_3312_);
lean_closure_set(v___f_3313_, 7, v_attrName_3274_);
v___x_3314_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3313_, v___x_3282_, v___x_3291_, v___x_3296_, v___y_3278_, v___y_3279_);
lean_dec_ref_known(v___x_3291_, 7);
v___y_3298_ = v___x_3314_;
goto v___jp_3297_;
}
else
{
lean_dec_ref_known(v___x_3291_, 7);
lean_dec(v_stx_3276_);
lean_dec(v_declName_3275_);
lean_dec(v_attrName_3274_);
lean_dec_ref(v_ext_3271_);
v___y_3298_ = v___x_3308_;
goto v___jp_3297_;
}
v___jp_3297_:
{
if (lean_obj_tag(v___y_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3307_; 
v_a_3299_ = lean_ctor_get(v___y_3298_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___y_3298_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3301_ = v___y_3298_;
v_isShared_3302_ = v_isSharedCheck_3307_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___y_3298_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3307_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3303_; lean_object* v___x_3305_; 
v___x_3303_ = lean_st_ref_get(v___x_3296_);
lean_dec(v___x_3296_);
lean_dec(v___x_3303_);
if (v_isShared_3302_ == 0)
{
v___x_3305_ = v___x_3301_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3299_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
else
{
lean_dec(v___x_3296_);
return v___y_3298_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v___x_3315_, lean_object* v_ext_3316_, lean_object* v_showInfo_3317_, lean_object* v_minIndexable_3318_, lean_object* v_attrName_3319_, lean_object* v_declName_3320_, lean_object* v_stx_3321_, lean_object* v_attrKind_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
uint8_t v_showInfo_boxed_3326_; uint8_t v_minIndexable_boxed_3327_; uint8_t v_attrKind_boxed_3328_; lean_object* v_res_3329_; 
v_showInfo_boxed_3326_ = lean_unbox(v_showInfo_3317_);
v_minIndexable_boxed_3327_ = lean_unbox(v_minIndexable_3318_);
v_attrKind_boxed_3328_ = lean_unbox(v_attrKind_3322_);
v_res_3329_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v___x_3315_, v_ext_3316_, v_showInfo_boxed_3326_, v_minIndexable_boxed_3327_, v_attrName_3319_, v_declName_3320_, v_stx_3321_, v_attrKind_boxed_3328_, v___y_3323_, v___y_3324_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3352_, uint8_t v_minIndexable_3353_, uint8_t v_showInfo_3354_, lean_object* v_ext_3355_, lean_object* v_ref_3356_){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___f_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___f_3363_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3409_; 
v___x_3358_ = lean_box(1);
v___x_3359_ = lean_box(v_showInfo_3354_);
lean_inc_n(v_attrName_3352_, 2);
lean_inc_ref(v_ext_3355_);
v___f_3360_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3360_, 0, v___x_3358_);
lean_closure_set(v___f_3360_, 1, v_ext_3355_);
lean_closure_set(v___f_3360_, 2, v___x_3359_);
lean_closure_set(v___f_3360_, 3, v_attrName_3352_);
v___x_3361_ = lean_box(v_showInfo_3354_);
v___x_3362_ = lean_box(v_minIndexable_3353_);
v___f_3363_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3363_, 0, v___x_3358_);
lean_closure_set(v___f_3363_, 1, v_ext_3355_);
lean_closure_set(v___f_3363_, 2, v___x_3361_);
lean_closure_set(v___f_3363_, 3, v___x_3362_);
lean_closure_set(v___f_3363_, 4, v_attrName_3352_);
if (v_minIndexable_3353_ == 0)
{
if (v_showInfo_3354_ == 0)
{
lean_inc(v_attrName_3352_);
v___y_3409_ = v_attrName_3352_;
goto v___jp_3408_;
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3352_);
v___x_3438_ = lean_name_append_after(v_attrName_3352_, v___x_3437_);
v___y_3409_ = v___x_3438_;
goto v___jp_3408_;
}
}
else
{
if (v_showInfo_3354_ == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3352_);
v___x_3440_ = lean_name_append_after(v_attrName_3352_, v___x_3439_);
v___y_3409_ = v___x_3440_;
goto v___jp_3408_;
}
else
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3352_);
v___x_3442_ = lean_name_append_after(v_attrName_3352_, v___x_3441_);
v___y_3409_ = v___x_3442_;
goto v___jp_3408_;
}
}
v___jp_3364_:
{
lean_object* v___x_3367_; uint8_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3368_ = 1;
v___x_3369_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3352_, v___x_3368_);
v___x_3370_ = lean_string_append(v___x_3367_, v___x_3369_);
v___x_3371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3372_ = lean_string_append(v___x_3370_, v___x_3371_);
v___x_3373_ = lean_string_append(v___x_3372_, v___x_3369_);
v___x_3374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3375_ = lean_string_append(v___x_3373_, v___x_3374_);
v___x_3376_ = lean_string_append(v___x_3375_, v___x_3369_);
v___x_3377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3378_ = lean_string_append(v___x_3376_, v___x_3377_);
v___x_3379_ = lean_string_append(v___x_3378_, v___x_3369_);
v___x_3380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3381_ = lean_string_append(v___x_3379_, v___x_3380_);
v___x_3382_ = lean_string_append(v___x_3381_, v___x_3369_);
v___x_3383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3384_ = lean_string_append(v___x_3382_, v___x_3383_);
v___x_3385_ = lean_string_append(v___x_3384_, v___x_3369_);
v___x_3386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3387_ = lean_string_append(v___x_3385_, v___x_3386_);
v___x_3388_ = lean_string_append(v___x_3387_, v___x_3369_);
v___x_3389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3390_ = lean_string_append(v___x_3388_, v___x_3389_);
v___x_3391_ = lean_string_append(v___x_3390_, v___x_3369_);
v___x_3392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3393_ = lean_string_append(v___x_3391_, v___x_3392_);
v___x_3394_ = lean_string_append(v___x_3393_, v___x_3369_);
v___x_3395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3396_ = lean_string_append(v___x_3394_, v___x_3395_);
v___x_3397_ = lean_string_append(v___x_3396_, v___x_3369_);
v___x_3398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3399_ = lean_string_append(v___x_3397_, v___x_3398_);
v___x_3400_ = lean_string_append(v___x_3399_, v___x_3369_);
lean_dec_ref(v___x_3369_);
v___x_3401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3402_ = lean_string_append(v___x_3400_, v___x_3401_);
v___x_3403_ = lean_string_append(v___y_3366_, v___x_3402_);
lean_dec_ref(v___x_3402_);
v___x_3404_ = 1;
v___x_3405_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3405_, 0, v_ref_3356_);
lean_ctor_set(v___x_3405_, 1, v___y_3365_);
lean_ctor_set(v___x_3405_, 2, v___x_3403_);
lean_ctor_set_uint8(v___x_3405_, sizeof(void*)*3, v___x_3404_);
v___x_3406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v___f_3363_);
lean_ctor_set(v___x_3406_, 2, v___f_3360_);
v___x_3407_ = l_Lean_registerBuiltinAttribute(v___x_3406_);
return v___x_3407_;
}
v___jp_3408_:
{
if (v_minIndexable_3353_ == 0)
{
if (v_showInfo_3354_ == 0)
{
lean_object* v___x_3410_; uint8_t v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3411_ = 1;
lean_inc(v_attrName_3352_);
v___x_3412_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3352_, v___x_3411_);
v___x_3413_ = lean_string_append(v___x_3410_, v___x_3412_);
lean_dec_ref(v___x_3412_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3415_ = lean_string_append(v___x_3413_, v___x_3414_);
v___y_3365_ = v___y_3409_;
v___y_3366_ = v___x_3415_;
goto v___jp_3364_;
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3352_);
v___x_3417_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3352_, v_showInfo_3354_);
v___x_3418_ = lean_string_append(v___x_3416_, v___x_3417_);
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3420_ = lean_string_append(v___x_3418_, v___x_3419_);
v___x_3421_ = lean_string_append(v___x_3420_, v___x_3417_);
lean_dec_ref(v___x_3417_);
v___x_3422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3423_ = lean_string_append(v___x_3421_, v___x_3422_);
v___y_3365_ = v___y_3409_;
v___y_3366_ = v___x_3423_;
goto v___jp_3364_;
}
}
else
{
if (v_showInfo_3354_ == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3352_);
v___x_3425_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3352_, v_minIndexable_3353_);
v___x_3426_ = lean_string_append(v___x_3424_, v___x_3425_);
lean_dec_ref(v___x_3425_);
v___x_3427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3428_ = lean_string_append(v___x_3426_, v___x_3427_);
v___y_3365_ = v___y_3409_;
v___y_3366_ = v___x_3428_;
goto v___jp_3364_;
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3352_);
v___x_3430_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3352_, v_showInfo_3354_);
v___x_3431_ = lean_string_append(v___x_3429_, v___x_3430_);
v___x_3432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3433_ = lean_string_append(v___x_3431_, v___x_3432_);
v___x_3434_ = lean_string_append(v___x_3433_, v___x_3430_);
lean_dec_ref(v___x_3430_);
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3436_ = lean_string_append(v___x_3434_, v___x_3435_);
v___y_3365_ = v___y_3409_;
v___y_3366_ = v___x_3436_;
goto v___jp_3364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3443_, lean_object* v_minIndexable_3444_, lean_object* v_showInfo_3445_, lean_object* v_ext_3446_, lean_object* v_ref_3447_, lean_object* v_a_3448_){
_start:
{
uint8_t v_minIndexable_boxed_3449_; uint8_t v_showInfo_boxed_3450_; lean_object* v_res_3451_; 
v_minIndexable_boxed_3449_ = lean_unbox(v_minIndexable_3444_);
v_showInfo_boxed_3450_ = lean_unbox(v_showInfo_3445_);
v_res_3451_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3443_, v_minIndexable_boxed_3449_, v_showInfo_boxed_3450_, v_ext_3446_, v_ref_3447_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3452_, lean_object* v_msg_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v___x_3459_; 
v___x_3459_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3460_, lean_object* v_msg_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3460_, v_msg_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3468_, uint8_t v_attrKind_3469_, uint8_t v_showInfo_3470_, uint8_t v_minIndexable_3471_, lean_object* v_as_3472_, lean_object* v_as_x27_3473_, lean_object* v_b_3474_, lean_object* v_a_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v___x_3481_; 
v___x_3481_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3468_, v_attrKind_3469_, v_showInfo_3470_, v_minIndexable_3471_, v_as_x27_3473_, v_b_3474_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3482_, lean_object* v_attrKind_3483_, lean_object* v_showInfo_3484_, lean_object* v_minIndexable_3485_, lean_object* v_as_3486_, lean_object* v_as_x27_3487_, lean_object* v_b_3488_, lean_object* v_a_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
uint8_t v_attrKind_boxed_3495_; uint8_t v_showInfo_boxed_3496_; uint8_t v_minIndexable_boxed_3497_; lean_object* v_res_3498_; 
v_attrKind_boxed_3495_ = lean_unbox(v_attrKind_3483_);
v_showInfo_boxed_3496_ = lean_unbox(v_showInfo_3484_);
v_minIndexable_boxed_3497_ = lean_unbox(v_minIndexable_3485_);
v_res_3498_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3482_, v_attrKind_boxed_3495_, v_showInfo_boxed_3496_, v_minIndexable_boxed_3497_, v_as_3486_, v_as_x27_3487_, v_b_3488_, v_a_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v_as_x27_3487_);
lean_dec(v_as_3486_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3499_, lean_object* v_x_3500_, uint8_t v_isExporting_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v___x_3507_; 
v___x_3507_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3500_, v_isExporting_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3508_, lean_object* v_x_3509_, lean_object* v_isExporting_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
uint8_t v_isExporting_boxed_3516_; lean_object* v_res_3517_; 
v_isExporting_boxed_3516_ = lean_unbox(v_isExporting_3510_);
v_res_3517_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3508_, v_x_3509_, v_isExporting_boxed_3516_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3518_, lean_object* v_x_3519_, uint8_t v_when_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3519_, v_when_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3527_, lean_object* v_x_3528_, lean_object* v_when_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
uint8_t v_when_boxed_3535_; lean_object* v_res_3536_; 
v_when_boxed_3535_ = lean_unbox(v_when_3529_);
v_res_3536_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3527_, v_x_3528_, v_when_boxed_3535_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3537_, lean_object* v_m_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3538_, v_a_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3541_, lean_object* v_m_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3541_, v_m_3542_, v_a_3543_);
lean_dec(v_a_3543_);
lean_dec_ref(v_m_3542_);
return v_res_3544_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3545_, lean_object* v_x_3546_, lean_object* v_x_3547_){
_start:
{
uint8_t v___x_3548_; 
v___x_3548_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3546_, v_x_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3549_, lean_object* v_x_3550_, lean_object* v_x_3551_){
_start:
{
uint8_t v_res_3552_; lean_object* v_r_3553_; 
v_res_3552_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3549_, v_x_3550_, v_x_3551_);
lean_dec_ref(v_x_3551_);
lean_dec_ref(v_x_3550_);
v_r_3553_ = lean_box(v_res_3552_);
return v_r_3553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3554_, lean_object* v_a_3555_, lean_object* v_x_3556_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3555_, v_x_3556_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3558_, lean_object* v_a_3559_, lean_object* v_x_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(v_00_u03b2_3558_, v_a_3559_, v_x_3560_);
lean_dec(v_x_3560_);
lean_dec(v_a_3559_);
return v_res_3561_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3562_, lean_object* v_x_3563_, size_t v_x_3564_, lean_object* v_x_3565_){
_start:
{
uint8_t v___x_3566_; 
v___x_3566_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3563_, v_x_3564_, v_x_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3567_, lean_object* v_x_3568_, lean_object* v_x_3569_, lean_object* v_x_3570_){
_start:
{
size_t v_x_17587__boxed_3571_; uint8_t v_res_3572_; lean_object* v_r_3573_; 
v_x_17587__boxed_3571_ = lean_unbox_usize(v_x_3569_);
lean_dec(v_x_3569_);
v_res_3572_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3567_, v_x_3568_, v_x_17587__boxed_3571_, v_x_3570_);
lean_dec_ref(v_x_3570_);
lean_dec_ref(v_x_3568_);
v_r_3573_ = lean_box(v_res_3572_);
return v_r_3573_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_3574_, lean_object* v_keys_3575_, lean_object* v_vals_3576_, lean_object* v_heq_3577_, lean_object* v_i_3578_, lean_object* v_k_3579_){
_start:
{
uint8_t v___x_3580_; 
v___x_3580_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_3575_, v_i_3578_, v_k_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3581_, lean_object* v_keys_3582_, lean_object* v_vals_3583_, lean_object* v_heq_3584_, lean_object* v_i_3585_, lean_object* v_k_3586_){
_start:
{
uint8_t v_res_3587_; lean_object* v_r_3588_; 
v_res_3587_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(v_00_u03b2_3581_, v_keys_3582_, v_vals_3583_, v_heq_3584_, v_i_3585_, v_k_3586_);
lean_dec_ref(v_k_3586_);
lean_dec_ref(v_vals_3583_);
lean_dec_ref(v_keys_3582_);
v_r_3588_ = lean_box(v_res_3587_);
return v_r_3588_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3589_ = lean_box(0);
v___x_3590_ = lean_unsigned_to_nat(16u);
v___x_3591_ = lean_mk_array(v___x_3590_, v___x_3589_);
return v___x_3591_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3592_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3593_ = lean_unsigned_to_nat(0u);
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
lean_ctor_set(v___x_3594_, 1, v___x_3592_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3596_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3597_ = lean_st_mk_ref(v___x_3596_);
v___x_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3601_, lean_object* v_msg_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v_ref_3606_; lean_object* v___x_3607_; lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3652_; 
v_ref_3606_ = lean_ctor_get(v___y_3603_, 5);
v___x_3607_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3602_, v___y_3603_, v___y_3604_);
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3610_ = v___x_3607_;
v_isShared_3611_ = v_isSharedCheck_3652_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3652_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v_traceState_3613_; lean_object* v_env_3614_; lean_object* v_nextMacroScope_3615_; lean_object* v_ngen_3616_; lean_object* v_auxDeclNGen_3617_; lean_object* v_cache_3618_; lean_object* v_messages_3619_; lean_object* v_infoState_3620_; lean_object* v_snapshotTasks_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3651_; 
v___x_3612_ = lean_st_ref_take(v___y_3604_);
v_traceState_3613_ = lean_ctor_get(v___x_3612_, 4);
v_env_3614_ = lean_ctor_get(v___x_3612_, 0);
v_nextMacroScope_3615_ = lean_ctor_get(v___x_3612_, 1);
v_ngen_3616_ = lean_ctor_get(v___x_3612_, 2);
v_auxDeclNGen_3617_ = lean_ctor_get(v___x_3612_, 3);
v_cache_3618_ = lean_ctor_get(v___x_3612_, 5);
v_messages_3619_ = lean_ctor_get(v___x_3612_, 6);
v_infoState_3620_ = lean_ctor_get(v___x_3612_, 7);
v_snapshotTasks_3621_ = lean_ctor_get(v___x_3612_, 8);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3623_ = v___x_3612_;
v_isShared_3624_ = v_isSharedCheck_3651_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_snapshotTasks_3621_);
lean_inc(v_infoState_3620_);
lean_inc(v_messages_3619_);
lean_inc(v_cache_3618_);
lean_inc(v_traceState_3613_);
lean_inc(v_auxDeclNGen_3617_);
lean_inc(v_ngen_3616_);
lean_inc(v_nextMacroScope_3615_);
lean_inc(v_env_3614_);
lean_dec(v___x_3612_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3651_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
uint64_t v_tid_3625_; lean_object* v_traces_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3650_; 
v_tid_3625_ = lean_ctor_get_uint64(v_traceState_3613_, sizeof(void*)*1);
v_traces_3626_ = lean_ctor_get(v_traceState_3613_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_traceState_3613_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3628_ = v_traceState_3613_;
v_isShared_3629_ = v_isSharedCheck_3650_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_traces_3626_);
lean_dec(v_traceState_3613_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3650_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; double v___x_3631_; uint8_t v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3640_; 
v___x_3630_ = lean_box(0);
v___x_3631_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_3632_ = 0;
v___x_3633_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_3634_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3634_, 0, v_cls_3601_);
lean_ctor_set(v___x_3634_, 1, v___x_3630_);
lean_ctor_set(v___x_3634_, 2, v___x_3633_);
lean_ctor_set_float(v___x_3634_, sizeof(void*)*3, v___x_3631_);
lean_ctor_set_float(v___x_3634_, sizeof(void*)*3 + 8, v___x_3631_);
lean_ctor_set_uint8(v___x_3634_, sizeof(void*)*3 + 16, v___x_3632_);
v___x_3635_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_3636_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3634_);
lean_ctor_set(v___x_3636_, 1, v_a_3608_);
lean_ctor_set(v___x_3636_, 2, v___x_3635_);
lean_inc(v_ref_3606_);
v___x_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3637_, 0, v_ref_3606_);
lean_ctor_set(v___x_3637_, 1, v___x_3636_);
v___x_3638_ = l_Lean_PersistentArray_push___redArg(v_traces_3626_, v___x_3637_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 0, v___x_3638_);
v___x_3640_ = v___x_3628_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3638_);
lean_ctor_set_uint64(v_reuseFailAlloc_3649_, sizeof(void*)*1, v_tid_3625_);
v___x_3640_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3642_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v___x_3640_);
v___x_3642_ = v___x_3623_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_env_3614_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_nextMacroScope_3615_);
lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_ngen_3616_);
lean_ctor_set(v_reuseFailAlloc_3648_, 3, v_auxDeclNGen_3617_);
lean_ctor_set(v_reuseFailAlloc_3648_, 4, v___x_3640_);
lean_ctor_set(v_reuseFailAlloc_3648_, 5, v_cache_3618_);
lean_ctor_set(v_reuseFailAlloc_3648_, 6, v_messages_3619_);
lean_ctor_set(v_reuseFailAlloc_3648_, 7, v_infoState_3620_);
lean_ctor_set(v_reuseFailAlloc_3648_, 8, v_snapshotTasks_3621_);
v___x_3642_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3646_; 
v___x_3643_ = lean_st_ref_set(v___y_3604_, v___x_3642_);
v___x_3644_ = lean_box(0);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3644_);
v___x_3646_ = v___x_3610_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3653_, lean_object* v_msg_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3653_, v_msg_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3659_, uint8_t v_isMeta_3660_, lean_object* v_hint_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3665_; lean_object* v_env_3666_; uint8_t v_isExporting_3667_; lean_object* v___x_3668_; lean_object* v_env_3669_; lean_object* v___x_3670_; lean_object* v_entry_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___y_3676_; lean_object* v___x_3701_; uint8_t v___x_3702_; 
v___x_3665_ = lean_st_ref_get(v___y_3663_);
v_env_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc_ref(v_env_3666_);
lean_dec(v___x_3665_);
v_isExporting_3667_ = lean_ctor_get_uint8(v_env_3666_, sizeof(void*)*8);
lean_dec_ref(v_env_3666_);
v___x_3668_ = lean_st_ref_get(v___y_3663_);
v_env_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc_ref(v_env_3669_);
lean_dec(v___x_3668_);
v___x_3670_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_3659_);
v_entry_3671_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3671_, 0, v_mod_3659_);
lean_ctor_set_uint8(v_entry_3671_, sizeof(void*)*1, v_isExporting_3667_);
lean_ctor_set_uint8(v_entry_3671_, sizeof(void*)*1 + 1, v_isMeta_3660_);
v___x_3672_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3673_ = lean_box(1);
v___x_3674_ = lean_box(0);
v___x_3701_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3670_, v___x_3672_, v_env_3669_, v___x_3673_, v___x_3674_);
v___x_3702_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3701_, v_entry_3671_);
lean_dec(v___x_3701_);
if (v___x_3702_ == 0)
{
lean_object* v_options_3703_; uint8_t v_hasTrace_3704_; 
v_options_3703_ = lean_ctor_get(v___y_3662_, 2);
v_hasTrace_3704_ = lean_ctor_get_uint8(v_options_3703_, sizeof(void*)*1);
if (v_hasTrace_3704_ == 0)
{
lean_dec(v_hint_3661_);
lean_dec(v_mod_3659_);
v___y_3676_ = v___y_3663_;
goto v___jp_3675_;
}
else
{
lean_object* v_inheritedTraceOptions_3705_; lean_object* v_cls_3706_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___x_3726_; uint8_t v___x_3727_; 
v_inheritedTraceOptions_3705_ = lean_ctor_get(v___y_3662_, 13);
v_cls_3706_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_3726_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_3727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3705_, v_options_3703_, v___x_3726_);
if (v___x_3727_ == 0)
{
lean_dec(v_hint_3661_);
lean_dec(v_mod_3659_);
v___y_3676_ = v___y_3663_;
goto v___jp_3675_;
}
else
{
lean_object* v___x_3728_; lean_object* v___y_3730_; 
v___x_3728_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_3667_ == 0)
{
lean_object* v___x_3737_; 
v___x_3737_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_3730_ = v___x_3737_;
goto v___jp_3729_;
}
else
{
lean_object* v___x_3738_; 
v___x_3738_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_3730_ = v___x_3738_;
goto v___jp_3729_;
}
v___jp_3729_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_inc_ref(v___y_3730_);
v___x_3731_ = l_Lean_stringToMessageData(v___y_3730_);
v___x_3732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3728_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
if (v_isMeta_3660_ == 0)
{
lean_object* v___x_3735_; 
v___x_3735_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3713_ = v___x_3734_;
v___y_3714_ = v___x_3735_;
goto v___jp_3712_;
}
else
{
lean_object* v___x_3736_; 
v___x_3736_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3713_ = v___x_3734_;
v___y_3714_ = v___x_3736_;
goto v___jp_3712_;
}
}
}
v___jp_3707_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___y_3708_);
lean_ctor_set(v___x_3710_, 1, v___y_3709_);
v___x_3711_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3706_, v___x_3710_, v___y_3662_, v___y_3663_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_dec_ref_known(v___x_3711_, 1);
v___y_3676_ = v___y_3663_;
goto v___jp_3675_;
}
else
{
lean_dec_ref_known(v_entry_3671_, 1);
return v___x_3711_;
}
}
v___jp_3712_:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
lean_inc_ref(v___y_3714_);
v___x_3715_ = l_Lean_stringToMessageData(v___y_3714_);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___y_3713_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = l_Lean_MessageData_ofName(v_mod_3659_);
v___x_3720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3718_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = l_Lean_Name_isAnonymous(v_hint_3661_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_3723_ = l_Lean_MessageData_ofName(v_hint_3661_);
v___x_3724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3722_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___y_3708_ = v___x_3720_;
v___y_3709_ = v___x_3724_;
goto v___jp_3707_;
}
else
{
lean_object* v___x_3725_; 
lean_dec(v_hint_3661_);
v___x_3725_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_3708_ = v___x_3720_;
v___y_3709_ = v___x_3725_;
goto v___jp_3707_;
}
}
}
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_dec_ref_known(v_entry_3671_, 1);
lean_dec(v_hint_3661_);
lean_dec(v_mod_3659_);
v___x_3739_ = lean_box(0);
v___x_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
return v___x_3740_;
}
v___jp_3675_:
{
lean_object* v___x_3677_; lean_object* v_toEnvExtension_3678_; lean_object* v_env_3679_; lean_object* v_nextMacroScope_3680_; lean_object* v_ngen_3681_; lean_object* v_auxDeclNGen_3682_; lean_object* v_traceState_3683_; lean_object* v_messages_3684_; lean_object* v_infoState_3685_; lean_object* v_snapshotTasks_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3699_; 
v___x_3677_ = lean_st_ref_take(v___y_3676_);
v_toEnvExtension_3678_ = lean_ctor_get(v___x_3672_, 0);
v_env_3679_ = lean_ctor_get(v___x_3677_, 0);
v_nextMacroScope_3680_ = lean_ctor_get(v___x_3677_, 1);
v_ngen_3681_ = lean_ctor_get(v___x_3677_, 2);
v_auxDeclNGen_3682_ = lean_ctor_get(v___x_3677_, 3);
v_traceState_3683_ = lean_ctor_get(v___x_3677_, 4);
v_messages_3684_ = lean_ctor_get(v___x_3677_, 6);
v_infoState_3685_ = lean_ctor_get(v___x_3677_, 7);
v_snapshotTasks_3686_ = lean_ctor_get(v___x_3677_, 8);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; 
v_unused_3700_ = lean_ctor_get(v___x_3677_, 5);
lean_dec(v_unused_3700_);
v___x_3688_ = v___x_3677_;
v_isShared_3689_ = v_isSharedCheck_3699_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_snapshotTasks_3686_);
lean_inc(v_infoState_3685_);
lean_inc(v_messages_3684_);
lean_inc(v_traceState_3683_);
lean_inc(v_auxDeclNGen_3682_);
lean_inc(v_ngen_3681_);
lean_inc(v_nextMacroScope_3680_);
lean_inc(v_env_3679_);
lean_dec(v___x_3677_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3699_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v_asyncMode_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
v_asyncMode_3690_ = lean_ctor_get(v_toEnvExtension_3678_, 2);
v___x_3691_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3672_, v_env_3679_, v_entry_3671_, v_asyncMode_3690_, v___x_3674_);
v___x_3692_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 5, v___x_3692_);
lean_ctor_set(v___x_3688_, 0, v___x_3691_);
v___x_3694_ = v___x_3688_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_nextMacroScope_3680_);
lean_ctor_set(v_reuseFailAlloc_3698_, 2, v_ngen_3681_);
lean_ctor_set(v_reuseFailAlloc_3698_, 3, v_auxDeclNGen_3682_);
lean_ctor_set(v_reuseFailAlloc_3698_, 4, v_traceState_3683_);
lean_ctor_set(v_reuseFailAlloc_3698_, 5, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3698_, 6, v_messages_3684_);
lean_ctor_set(v_reuseFailAlloc_3698_, 7, v_infoState_3685_);
lean_ctor_set(v_reuseFailAlloc_3698_, 8, v_snapshotTasks_3686_);
v___x_3694_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3695_ = lean_st_ref_set(v___y_3676_, v___x_3694_);
v___x_3696_ = lean_box(0);
v___x_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
return v___x_3697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3741_, lean_object* v_isMeta_3742_, lean_object* v_hint_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
uint8_t v_isMeta_boxed_3747_; lean_object* v_res_3748_; 
v_isMeta_boxed_3747_ = lean_unbox(v_isMeta_3742_);
v_res_3748_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3741_, v_isMeta_boxed_3747_, v_hint_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3749_, lean_object* v_declName_3750_, lean_object* v_as_3751_, size_t v_sz_3752_, size_t v_i_3753_, lean_object* v_b_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
uint8_t v___x_3758_; 
v___x_3758_ = lean_usize_dec_lt(v_i_3753_, v_sz_3752_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; 
lean_dec(v_declName_3750_);
v___x_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3759_, 0, v_b_3754_);
return v___x_3759_;
}
else
{
lean_object* v___x_3760_; lean_object* v_modules_3761_; lean_object* v___x_3762_; lean_object* v_a_3763_; lean_object* v___x_3764_; lean_object* v_toImport_3765_; lean_object* v_module_3766_; uint8_t v___x_3767_; lean_object* v___x_3768_; 
v___x_3760_ = l_Lean_Environment_header(v___x_3749_);
v_modules_3761_ = lean_ctor_get(v___x_3760_, 3);
lean_inc_ref(v_modules_3761_);
lean_dec_ref(v___x_3760_);
v___x_3762_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3763_ = lean_array_uget_borrowed(v_as_3751_, v_i_3753_);
v___x_3764_ = lean_array_get(v___x_3762_, v_modules_3761_, v_a_3763_);
lean_dec_ref(v_modules_3761_);
v_toImport_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc_ref(v_toImport_3765_);
lean_dec(v___x_3764_);
v_module_3766_ = lean_ctor_get(v_toImport_3765_, 0);
lean_inc(v_module_3766_);
lean_dec_ref(v_toImport_3765_);
v___x_3767_ = 0;
lean_inc(v_declName_3750_);
v___x_3768_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3766_, v___x_3767_, v_declName_3750_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v___x_3769_; size_t v___x_3770_; size_t v___x_3771_; 
lean_dec_ref_known(v___x_3768_, 1);
v___x_3769_ = lean_box(0);
v___x_3770_ = ((size_t)1ULL);
v___x_3771_ = lean_usize_add(v_i_3753_, v___x_3770_);
v_i_3753_ = v___x_3771_;
v_b_3754_ = v___x_3769_;
goto _start;
}
else
{
lean_dec(v_declName_3750_);
return v___x_3768_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3773_, lean_object* v_declName_3774_, lean_object* v_as_3775_, lean_object* v_sz_3776_, lean_object* v_i_3777_, lean_object* v_b_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
size_t v_sz_boxed_3782_; size_t v_i_boxed_3783_; lean_object* v_res_3784_; 
v_sz_boxed_3782_ = lean_unbox_usize(v_sz_3776_);
lean_dec(v_sz_3776_);
v_i_boxed_3783_ = lean_unbox_usize(v_i_3777_);
lean_dec(v_i_3777_);
v_res_3784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3773_, v_declName_3774_, v_as_3775_, v_sz_boxed_3782_, v_i_boxed_3783_, v_b_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec_ref(v_as_3775_);
lean_dec_ref(v___x_3773_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3785_, uint8_t v_isMeta_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; lean_object* v_env_3794_; lean_object* v___y_3796_; lean_object* v___x_3809_; 
v___x_3790_ = lean_st_ref_get(v___y_3788_);
v_env_3794_ = lean_ctor_get(v___x_3790_, 0);
lean_inc_ref(v_env_3794_);
lean_dec(v___x_3790_);
v___x_3809_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3794_, v_declName_3785_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_dec_ref(v_env_3794_);
lean_dec(v_declName_3785_);
goto v___jp_3791_;
}
else
{
lean_object* v_val_3810_; lean_object* v___x_3811_; lean_object* v_modules_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v_val_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_val_3810_);
lean_dec_ref_known(v___x_3809_, 1);
v___x_3811_ = l_Lean_Environment_header(v_env_3794_);
v_modules_3812_ = lean_ctor_get(v___x_3811_, 3);
lean_inc_ref(v_modules_3812_);
lean_dec_ref(v___x_3811_);
v___x_3813_ = lean_array_get_size(v_modules_3812_);
v___x_3814_ = lean_nat_dec_lt(v_val_3810_, v___x_3813_);
if (v___x_3814_ == 0)
{
lean_dec_ref(v_modules_3812_);
lean_dec(v_val_3810_);
lean_dec_ref(v_env_3794_);
lean_dec(v_declName_3785_);
goto v___jp_3791_;
}
else
{
lean_object* v___x_3815_; lean_object* v_env_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; uint8_t v___y_3820_; 
v___x_3815_ = lean_st_ref_get(v___y_3788_);
v_env_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc_ref(v_env_3816_);
lean_dec(v___x_3815_);
v___x_3817_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3818_ = lean_array_fget(v_modules_3812_, v_val_3810_);
lean_dec(v_val_3810_);
lean_dec_ref(v_modules_3812_);
if (v_isMeta_3786_ == 0)
{
lean_dec_ref(v_env_3816_);
v___y_3820_ = v_isMeta_3786_;
goto v___jp_3819_;
}
else
{
uint8_t v___x_3831_; 
lean_inc(v_declName_3785_);
v___x_3831_ = l_Lean_isMarkedMeta(v_env_3816_, v_declName_3785_);
if (v___x_3831_ == 0)
{
v___y_3820_ = v_isMeta_3786_;
goto v___jp_3819_;
}
else
{
uint8_t v___x_3832_; 
v___x_3832_ = 0;
v___y_3820_ = v___x_3832_;
goto v___jp_3819_;
}
}
v___jp_3819_:
{
lean_object* v_toImport_3821_; lean_object* v_module_3822_; lean_object* v___x_3823_; 
v_toImport_3821_ = lean_ctor_get(v___x_3818_, 0);
lean_inc_ref(v_toImport_3821_);
lean_dec(v___x_3818_);
v_module_3822_ = lean_ctor_get(v_toImport_3821_, 0);
lean_inc(v_module_3822_);
lean_dec_ref(v_toImport_3821_);
lean_inc(v_declName_3785_);
v___x_3823_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3822_, v___y_3820_, v_declName_3785_, v___y_3787_, v___y_3788_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
lean_dec_ref_known(v___x_3823_, 1);
v___x_3824_ = l_Lean_indirectModUseExt;
v___x_3825_ = lean_box(1);
v___x_3826_ = lean_box(0);
lean_inc_ref(v_env_3794_);
v___x_3827_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3817_, v___x_3824_, v_env_3794_, v___x_3825_, v___x_3826_);
v___x_3828_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3827_, v_declName_3785_);
lean_dec(v___x_3827_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v___x_3829_; 
v___x_3829_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3796_ = v___x_3829_;
goto v___jp_3795_;
}
else
{
lean_object* v_val_3830_; 
v_val_3830_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_val_3830_);
lean_dec_ref_known(v___x_3828_, 1);
v___y_3796_ = v_val_3830_;
goto v___jp_3795_;
}
}
else
{
lean_dec_ref(v_env_3794_);
lean_dec(v_declName_3785_);
return v___x_3823_;
}
}
}
}
v___jp_3791_:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3792_ = lean_box(0);
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
return v___x_3793_;
}
v___jp_3795_:
{
lean_object* v___x_3797_; size_t v_sz_3798_; size_t v___x_3799_; lean_object* v___x_3800_; 
v___x_3797_ = lean_box(0);
v_sz_3798_ = lean_array_size(v___y_3796_);
v___x_3799_ = ((size_t)0ULL);
v___x_3800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3794_, v_declName_3785_, v___y_3796_, v_sz_3798_, v___x_3799_, v___x_3797_, v___y_3787_, v___y_3788_);
lean_dec_ref(v___y_3796_);
lean_dec_ref(v_env_3794_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3807_ == 0)
{
lean_object* v_unused_3808_; 
v_unused_3808_ = lean_ctor_get(v___x_3800_, 0);
lean_dec(v_unused_3808_);
v___x_3802_ = v___x_3800_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_dec(v___x_3800_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v___x_3797_);
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3797_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
else
{
return v___x_3800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3833_, lean_object* v_isMeta_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
uint8_t v_isMeta_boxed_3838_; lean_object* v_res_3839_; 
v_isMeta_boxed_3838_ = lean_unbox(v_isMeta_3834_);
v_res_3839_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3833_, v_isMeta_boxed_3838_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_){
_start:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3844_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3845_ = lean_st_ref_get(v___x_3844_);
v___x_3846_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3845_, v_attrName_3840_);
lean_dec(v___x_3845_);
if (lean_obj_tag(v___x_3846_) == 1)
{
lean_object* v_val_3847_; lean_object* v_ext_3848_; lean_object* v_name_3849_; uint8_t v___x_3850_; lean_object* v___x_3851_; 
v_val_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_val_3847_);
v_ext_3848_ = lean_ctor_get(v_val_3847_, 1);
lean_inc_ref(v_ext_3848_);
lean_dec(v_val_3847_);
v_name_3849_ = lean_ctor_get(v_ext_3848_, 1);
lean_inc(v_name_3849_);
lean_dec_ref(v_ext_3848_);
v___x_3850_ = 1;
v___x_3851_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3849_, v___x_3850_, v_a_3841_, v_a_3842_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3858_ == 0)
{
lean_object* v_unused_3859_; 
v_unused_3859_ = lean_ctor_get(v___x_3851_, 0);
lean_dec(v_unused_3859_);
v___x_3853_ = v___x_3851_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_dec(v___x_3851_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 0, v___x_3846_);
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3846_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref_known(v___x_3846_, 1);
v_a_3860_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3851_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3851_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3846_);
return v___x_3868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3869_, v_a_3870_, v_a_3871_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
lean_dec(v_attrName_3869_);
return v_res_3873_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3875_, lean_object* v_x_3876_){
_start:
{
if (lean_obj_tag(v_x_3876_) == 0)
{
return v_x_3875_;
}
else
{
lean_object* v_key_3877_; lean_object* v_value_3878_; lean_object* v_tail_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3905_; 
v_key_3877_ = lean_ctor_get(v_x_3876_, 0);
v_value_3878_ = lean_ctor_get(v_x_3876_, 1);
v_tail_3879_ = lean_ctor_get(v_x_3876_, 2);
v_isSharedCheck_3905_ = !lean_is_exclusive(v_x_3876_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3881_ = v_x_3876_;
v_isShared_3882_ = v_isSharedCheck_3905_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_tail_3879_);
lean_inc(v_value_3878_);
lean_inc(v_key_3877_);
lean_dec(v_x_3876_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3905_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; uint64_t v___y_3885_; 
v___x_3883_ = lean_array_get_size(v_x_3875_);
if (lean_obj_tag(v_key_3877_) == 0)
{
uint64_t v___x_3903_; 
v___x_3903_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3885_ = v___x_3903_;
goto v___jp_3884_;
}
else
{
uint64_t v_hash_3904_; 
v_hash_3904_ = lean_ctor_get_uint64(v_key_3877_, sizeof(void*)*2);
v___y_3885_ = v_hash_3904_;
goto v___jp_3884_;
}
v___jp_3884_:
{
uint64_t v___x_3886_; uint64_t v___x_3887_; uint64_t v_fold_3888_; uint64_t v___x_3889_; uint64_t v___x_3890_; uint64_t v___x_3891_; size_t v___x_3892_; size_t v___x_3893_; size_t v___x_3894_; size_t v___x_3895_; size_t v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3899_; 
v___x_3886_ = 32ULL;
v___x_3887_ = lean_uint64_shift_right(v___y_3885_, v___x_3886_);
v_fold_3888_ = lean_uint64_xor(v___y_3885_, v___x_3887_);
v___x_3889_ = 16ULL;
v___x_3890_ = lean_uint64_shift_right(v_fold_3888_, v___x_3889_);
v___x_3891_ = lean_uint64_xor(v_fold_3888_, v___x_3890_);
v___x_3892_ = lean_uint64_to_usize(v___x_3891_);
v___x_3893_ = lean_usize_of_nat(v___x_3883_);
v___x_3894_ = ((size_t)1ULL);
v___x_3895_ = lean_usize_sub(v___x_3893_, v___x_3894_);
v___x_3896_ = lean_usize_land(v___x_3892_, v___x_3895_);
v___x_3897_ = lean_array_uget_borrowed(v_x_3875_, v___x_3896_);
lean_inc(v___x_3897_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 2, v___x_3897_);
v___x_3899_ = v___x_3881_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_key_3877_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_value_3878_);
lean_ctor_set(v_reuseFailAlloc_3902_, 2, v___x_3897_);
v___x_3899_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
lean_object* v___x_3900_; 
v___x_3900_ = lean_array_uset(v_x_3875_, v___x_3896_, v___x_3899_);
v_x_3875_ = v___x_3900_;
v_x_3876_ = v_tail_3879_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3906_, lean_object* v_source_3907_, lean_object* v_target_3908_){
_start:
{
lean_object* v___x_3909_; uint8_t v___x_3910_; 
v___x_3909_ = lean_array_get_size(v_source_3907_);
v___x_3910_ = lean_nat_dec_lt(v_i_3906_, v___x_3909_);
if (v___x_3910_ == 0)
{
lean_dec_ref(v_source_3907_);
lean_dec(v_i_3906_);
return v_target_3908_;
}
else
{
lean_object* v_es_3911_; lean_object* v___x_3912_; lean_object* v_source_3913_; lean_object* v_target_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_es_3911_ = lean_array_fget(v_source_3907_, v_i_3906_);
v___x_3912_ = lean_box(0);
v_source_3913_ = lean_array_fset(v_source_3907_, v_i_3906_, v___x_3912_);
v_target_3914_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3908_, v_es_3911_);
v___x_3915_ = lean_unsigned_to_nat(1u);
v___x_3916_ = lean_nat_add(v_i_3906_, v___x_3915_);
lean_dec(v_i_3906_);
v_i_3906_ = v___x_3916_;
v_source_3907_ = v_source_3913_;
v_target_3908_ = v_target_3914_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_3918_){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v_nbuckets_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3919_ = lean_array_get_size(v_data_3918_);
v___x_3920_ = lean_unsigned_to_nat(2u);
v_nbuckets_3921_ = lean_nat_mul(v___x_3919_, v___x_3920_);
v___x_3922_ = lean_unsigned_to_nat(0u);
v___x_3923_ = lean_box(0);
v___x_3924_ = lean_mk_array(v_nbuckets_3921_, v___x_3923_);
v___x_3925_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_3922_, v_data_3918_, v___x_3924_);
return v___x_3925_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_3926_, lean_object* v_x_3927_){
_start:
{
if (lean_obj_tag(v_x_3927_) == 0)
{
uint8_t v___x_3928_; 
v___x_3928_ = 0;
return v___x_3928_;
}
else
{
lean_object* v_key_3929_; lean_object* v_tail_3930_; uint8_t v___x_3931_; 
v_key_3929_ = lean_ctor_get(v_x_3927_, 0);
v_tail_3930_ = lean_ctor_get(v_x_3927_, 2);
v___x_3931_ = lean_name_eq(v_key_3929_, v_a_3926_);
if (v___x_3931_ == 0)
{
v_x_3927_ = v_tail_3930_;
goto _start;
}
else
{
return v___x_3931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_3933_, lean_object* v_x_3934_){
_start:
{
uint8_t v_res_3935_; lean_object* v_r_3936_; 
v_res_3935_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3933_, v_x_3934_);
lean_dec(v_x_3934_);
lean_dec(v_a_3933_);
v_r_3936_ = lean_box(v_res_3935_);
return v_r_3936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_3937_, lean_object* v_b_3938_, lean_object* v_x_3939_){
_start:
{
if (lean_obj_tag(v_x_3939_) == 0)
{
lean_dec(v_b_3938_);
lean_dec(v_a_3937_);
return v_x_3939_;
}
else
{
lean_object* v_key_3940_; lean_object* v_value_3941_; lean_object* v_tail_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3954_; 
v_key_3940_ = lean_ctor_get(v_x_3939_, 0);
v_value_3941_ = lean_ctor_get(v_x_3939_, 1);
v_tail_3942_ = lean_ctor_get(v_x_3939_, 2);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_x_3939_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3944_ = v_x_3939_;
v_isShared_3945_ = v_isSharedCheck_3954_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_tail_3942_);
lean_inc(v_value_3941_);
lean_inc(v_key_3940_);
lean_dec(v_x_3939_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3954_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
uint8_t v___x_3946_; 
v___x_3946_ = lean_name_eq(v_key_3940_, v_a_3937_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; lean_object* v___x_3949_; 
v___x_3947_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3937_, v_b_3938_, v_tail_3942_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 2, v___x_3947_);
v___x_3949_ = v___x_3944_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_key_3940_);
lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_value_3941_);
lean_ctor_set(v_reuseFailAlloc_3950_, 2, v___x_3947_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
else
{
lean_object* v___x_3952_; 
lean_dec(v_value_3941_);
lean_dec(v_key_3940_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 1, v_b_3938_);
lean_ctor_set(v___x_3944_, 0, v_a_3937_);
v___x_3952_ = v___x_3944_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3937_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_b_3938_);
lean_ctor_set(v_reuseFailAlloc_3953_, 2, v_tail_3942_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_3955_, lean_object* v_a_3956_, lean_object* v_b_3957_){
_start:
{
lean_object* v_size_3958_; lean_object* v_buckets_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_4005_; 
v_size_3958_ = lean_ctor_get(v_m_3955_, 0);
v_buckets_3959_ = lean_ctor_get(v_m_3955_, 1);
v_isSharedCheck_4005_ = !lean_is_exclusive(v_m_3955_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3961_ = v_m_3955_;
v_isShared_3962_ = v_isSharedCheck_4005_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_buckets_3959_);
lean_inc(v_size_3958_);
lean_dec(v_m_3955_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_4005_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3963_; uint64_t v___y_3965_; 
v___x_3963_ = lean_array_get_size(v_buckets_3959_);
if (lean_obj_tag(v_a_3956_) == 0)
{
uint64_t v___x_4003_; 
v___x_4003_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3965_ = v___x_4003_;
goto v___jp_3964_;
}
else
{
uint64_t v_hash_4004_; 
v_hash_4004_ = lean_ctor_get_uint64(v_a_3956_, sizeof(void*)*2);
v___y_3965_ = v_hash_4004_;
goto v___jp_3964_;
}
v___jp_3964_:
{
uint64_t v___x_3966_; uint64_t v___x_3967_; uint64_t v_fold_3968_; uint64_t v___x_3969_; uint64_t v___x_3970_; uint64_t v___x_3971_; size_t v___x_3972_; size_t v___x_3973_; size_t v___x_3974_; size_t v___x_3975_; size_t v___x_3976_; lean_object* v_bkt_3977_; uint8_t v___x_3978_; 
v___x_3966_ = 32ULL;
v___x_3967_ = lean_uint64_shift_right(v___y_3965_, v___x_3966_);
v_fold_3968_ = lean_uint64_xor(v___y_3965_, v___x_3967_);
v___x_3969_ = 16ULL;
v___x_3970_ = lean_uint64_shift_right(v_fold_3968_, v___x_3969_);
v___x_3971_ = lean_uint64_xor(v_fold_3968_, v___x_3970_);
v___x_3972_ = lean_uint64_to_usize(v___x_3971_);
v___x_3973_ = lean_usize_of_nat(v___x_3963_);
v___x_3974_ = ((size_t)1ULL);
v___x_3975_ = lean_usize_sub(v___x_3973_, v___x_3974_);
v___x_3976_ = lean_usize_land(v___x_3972_, v___x_3975_);
v_bkt_3977_ = lean_array_uget_borrowed(v_buckets_3959_, v___x_3976_);
v___x_3978_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3956_, v_bkt_3977_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; lean_object* v_size_x27_3980_; lean_object* v___x_3981_; lean_object* v_buckets_x27_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; uint8_t v___x_3988_; 
v___x_3979_ = lean_unsigned_to_nat(1u);
v_size_x27_3980_ = lean_nat_add(v_size_3958_, v___x_3979_);
lean_dec(v_size_3958_);
lean_inc(v_bkt_3977_);
v___x_3981_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3981_, 0, v_a_3956_);
lean_ctor_set(v___x_3981_, 1, v_b_3957_);
lean_ctor_set(v___x_3981_, 2, v_bkt_3977_);
v_buckets_x27_3982_ = lean_array_uset(v_buckets_3959_, v___x_3976_, v___x_3981_);
v___x_3983_ = lean_unsigned_to_nat(4u);
v___x_3984_ = lean_nat_mul(v_size_x27_3980_, v___x_3983_);
v___x_3985_ = lean_unsigned_to_nat(3u);
v___x_3986_ = lean_nat_div(v___x_3984_, v___x_3985_);
lean_dec(v___x_3984_);
v___x_3987_ = lean_array_get_size(v_buckets_x27_3982_);
v___x_3988_ = lean_nat_dec_le(v___x_3986_, v___x_3987_);
lean_dec(v___x_3986_);
if (v___x_3988_ == 0)
{
lean_object* v_val_3989_; lean_object* v___x_3991_; 
v_val_3989_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_3982_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v_val_3989_);
lean_ctor_set(v___x_3961_, 0, v_size_x27_3980_);
v___x_3991_ = v___x_3961_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_size_x27_3980_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_val_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
else
{
lean_object* v___x_3994_; 
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v_buckets_x27_3982_);
lean_ctor_set(v___x_3961_, 0, v_size_x27_3980_);
v___x_3994_ = v___x_3961_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_size_x27_3980_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v_buckets_x27_3982_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
else
{
lean_object* v___x_3996_; lean_object* v_buckets_x27_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4001_; 
lean_inc(v_bkt_3977_);
v___x_3996_ = lean_box(0);
v_buckets_x27_3997_ = lean_array_uset(v_buckets_3959_, v___x_3976_, v___x_3996_);
v___x_3998_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3956_, v_b_3957_, v_bkt_3977_);
v___x_3999_ = lean_array_uset(v_buckets_x27_3997_, v___x_3976_, v___x_3998_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v___x_3999_);
v___x_4001_ = v___x_3961_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_size_3958_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_4006_, lean_object* v_ref_4007_){
_start:
{
lean_object* v___x_4009_; 
lean_inc(v_ref_4007_);
v___x_4009_ = l_Lean_Meta_Grind_mkExtension(v_ref_4007_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; uint8_t v___x_4011_; uint8_t v___x_4012_; lean_object* v___x_4013_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc_n(v_a_4010_, 2);
lean_dec_ref_known(v___x_4009_, 1);
v___x_4011_ = 0;
v___x_4012_ = 1;
lean_inc(v_ref_4007_);
lean_inc(v_attrName_4006_);
v___x_4013_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4006_, v___x_4011_, v___x_4012_, v_a_4010_, v_ref_4007_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v___x_4014_; 
lean_dec_ref_known(v___x_4013_, 1);
lean_inc(v_ref_4007_);
lean_inc(v_a_4010_);
lean_inc(v_attrName_4006_);
v___x_4014_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4006_, v___x_4011_, v___x_4011_, v_a_4010_, v_ref_4007_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v___x_4015_; 
lean_dec_ref_known(v___x_4014_, 1);
lean_inc(v_ref_4007_);
lean_inc(v_a_4010_);
lean_inc(v_attrName_4006_);
v___x_4015_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4006_, v___x_4012_, v___x_4012_, v_a_4010_, v_ref_4007_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v___x_4016_; 
lean_dec_ref_known(v___x_4015_, 1);
lean_inc(v_a_4010_);
lean_inc(v_attrName_4006_);
v___x_4016_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4006_, v___x_4012_, v___x_4011_, v_a_4010_, v_ref_4007_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4027_; 
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4027_ == 0)
{
lean_object* v_unused_4028_; 
v_unused_4028_ = lean_ctor_get(v___x_4016_, 0);
lean_dec(v_unused_4028_);
v___x_4018_ = v___x_4016_;
v_isShared_4019_ = v_isSharedCheck_4027_;
goto v_resetjp_4017_;
}
else
{
lean_dec(v___x_4016_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4027_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4025_; 
v___x_4020_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4021_ = lean_st_ref_take(v___x_4020_);
lean_inc(v_a_4010_);
v___x_4022_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_4021_, v_attrName_4006_, v_a_4010_);
v___x_4023_ = lean_st_ref_set(v___x_4020_, v___x_4022_);
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 0, v_a_4010_);
v___x_4025_ = v___x_4018_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4010_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec(v_a_4010_);
lean_dec(v_attrName_4006_);
v_a_4029_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4016_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4016_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec(v_a_4010_);
lean_dec(v_ref_4007_);
lean_dec(v_attrName_4006_);
v_a_4037_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4015_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4015_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v_a_4010_);
lean_dec(v_ref_4007_);
lean_dec(v_attrName_4006_);
v_a_4045_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4014_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4014_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec(v_a_4010_);
lean_dec(v_ref_4007_);
lean_dec(v_attrName_4006_);
v_a_4053_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4013_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4013_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
else
{
lean_dec(v_ref_4007_);
lean_dec(v_attrName_4006_);
return v___x_4009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_4061_, lean_object* v_ref_4062_, lean_object* v_a_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Lean_Meta_Grind_registerAttr(v_attrName_4061_, v_ref_4062_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_4065_, lean_object* v_m_4066_, lean_object* v_a_4067_, lean_object* v_b_4068_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_4066_, v_a_4067_, v_b_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_4070_, lean_object* v_a_4071_, lean_object* v_x_4072_){
_start:
{
uint8_t v___x_4073_; 
v___x_4073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4071_, v_x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4074_, lean_object* v_a_4075_, lean_object* v_x_4076_){
_start:
{
uint8_t v_res_4077_; lean_object* v_r_4078_; 
v_res_4077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_4074_, v_a_4075_, v_x_4076_);
lean_dec(v_x_4076_);
lean_dec(v_a_4075_);
v_r_4078_ = lean_box(v_res_4077_);
return v_r_4078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_4079_, lean_object* v_data_4080_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4082_, lean_object* v_a_4083_, lean_object* v_b_4084_, lean_object* v_x_4085_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4083_, v_b_4084_, v_x_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4087_, lean_object* v_i_4088_, lean_object* v_source_4089_, lean_object* v_target_4090_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4088_, v_source_4089_, v_target_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4092_, lean_object* v_x_4093_, lean_object* v_x_4094_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4093_, v_x_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_4103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4104_ = l_Lean_Meta_Grind_registerAttr(v___x_4102_, v___x_4103_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4119_ = l_Lean_Meta_Grind_registerAttr(v___x_4117_, v___x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v___x_4125_; lean_object* v_env_4126_; lean_object* v___x_4127_; lean_object* v_ext_4128_; lean_object* v_toEnvExtension_4129_; lean_object* v_asyncMode_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v_casesTypes_4133_; uint8_t v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4125_ = lean_st_ref_get(v_a_4123_);
v_env_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc_ref(v_env_4126_);
lean_dec(v___x_4125_);
v___x_4127_ = l_Lean_Meta_Grind_grindExt;
v_ext_4128_ = lean_ctor_get(v___x_4127_, 1);
v_toEnvExtension_4129_ = lean_ctor_get(v_ext_4128_, 0);
v_asyncMode_4130_ = lean_ctor_get(v_toEnvExtension_4129_, 2);
v___x_4131_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4132_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4131_, v___x_4127_, v_env_4126_, v_asyncMode_4130_);
v_casesTypes_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc_ref(v_casesTypes_4133_);
lean_dec(v___x_4132_);
v___x_4134_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4133_, v_declName_4122_);
lean_dec_ref(v_casesTypes_4133_);
v___x_4135_ = lean_box(v___x_4134_);
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4137_, v_a_4138_);
lean_dec(v_a_4138_);
lean_dec(v_declName_4137_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4141_, v_a_4143_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4146_, v_a_4147_, v_a_4148_);
lean_dec(v_a_4148_);
lean_dec_ref(v_a_4147_);
lean_dec(v_declName_4146_);
return v_res_4150_;
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
