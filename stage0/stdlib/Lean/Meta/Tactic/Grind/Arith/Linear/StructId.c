// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.StructId
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.OrderInsts import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Arith.Linear.Var import Lean.Meta.Tactic.Grind.Arith.Insts import Init.Grind.Module.Envelope
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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`grind linarith` expected"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "\nto be definitionally equal to"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toIntModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 160, 55, 74, 32, 205, 206, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "One"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 85, 184, 168, 121, 55, 74, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 85, 184, 168, 121, 55, 74, 19)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(31, 134, 200, 93, 163, 253, 252, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OrderedRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 123, 155, 51, 122, 17, 247, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "type has a `Preorder` and is a `Semiring`, but is not an ordered ring, failed to synthesize"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NoNatZeroDivisors"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 29, 6, 12, 7, 77, 98, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__2(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "AddCommMonoid"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toZero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "zsmul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instHSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40_value),LEAN_SCALAR_PTR_LITERAL(131, 168, 246, 170, 1, 89, 173, 16)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "nsmul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "IsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toIsPreorder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48_value),LEAN_SCALAR_PTR_LITERAL(196, 84, 36, 174, 137, 182, 135, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49_value),LEAN_SCALAR_PTR_LITERAL(75, 224, 25, 76, 51, 82, 222, 202)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "IsLinearOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "toIsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52_value),LEAN_SCALAR_PTR_LITERAL(83, 108, 214, 71, 226, 119, 72, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toAddCommGroup"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value),LEAN_SCALAR_PTR_LITERAL(205, 72, 3, 192, 99, 106, 67, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "AddCommGroup"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "toAddCommMonoid"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value),LEAN_SCALAR_PTR_LITERAL(64, 158, 132, 153, 136, 140, 172, 182)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57_value),LEAN_SCALAR_PTR_LITERAL(143, 195, 31, 215, 150, 195, 138, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OrderedAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65_value),LEAN_SCALAR_PTR_LITERAL(93, 134, 71, 250, 19, 181, 172, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 228, 118, 74, 233, 69, 129, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(100, 80, 29, 215, 2, 174, 123, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind` unexpected failure, failure to initialize auxiliary `IntModule`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_13_; 
lean_inc(v_a_11_);
lean_inc_ref(v_a_10_);
lean_inc(v_a_9_);
lean_inc_ref(v_a_8_);
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v_a_3_);
lean_inc(v_a_2_);
v___x_13_ = lean_grind_canon(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_14_, v_a_7_);
return v___x_15_;
}
else
{
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___boxed(lean_object* v_e_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v_e_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec(v_a_17_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(lean_object* v_fn_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v_fn_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___boxed(lean_object* v_fn_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(v_fn_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec(v_a_46_);
lean_dec_ref(v_a_45_);
lean_dec(v_a_44_);
lean_dec(v_a_43_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(lean_object* v_c_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v_c_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
lean_dec_ref(v___x_67_);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_box(0);
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
lean_inc(v_a_63_);
lean_inc_ref(v_a_62_);
lean_inc(v_a_61_);
lean_inc_ref(v_a_60_);
lean_inc(v_a_59_);
lean_inc_ref(v_a_58_);
lean_inc(v_a_57_);
lean_inc(v_a_56_);
lean_inc(v_a_68_);
v___x_71_ = lean_grind_internalize(v_a_68_, v___x_69_, v___x_70_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v___x_71_, 0);
lean_dec(v_unused_79_);
v___x_73_ = v___x_71_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_dec(v___x_71_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v_a_68_);
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_68_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
else
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
lean_dec(v_a_68_);
v_a_80_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_87_ == 0)
{
v___x_82_ = v___x_71_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_71_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
else
{
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst___boxed(lean_object* v_c_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(v_c_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec(v_a_89_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(lean_object* v_c_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_113_; 
lean_inc(v_a_111_);
lean_inc_ref(v_a_110_);
lean_inc(v_a_109_);
lean_inc_ref(v_a_108_);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
lean_inc(v_a_103_);
lean_inc(v_a_102_);
v___x_113_ = lean_grind_canon(v_c_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_115_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref(v___x_113_);
v___x_115_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_114_, v_a_107_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref(v___x_115_);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_box(0);
lean_inc(v_a_111_);
lean_inc_ref(v_a_110_);
lean_inc(v_a_109_);
lean_inc_ref(v_a_108_);
lean_inc(v_a_107_);
lean_inc_ref(v_a_106_);
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
lean_inc(v_a_103_);
lean_inc(v_a_102_);
lean_inc(v_a_116_);
v___x_119_ = lean_grind_internalize(v_a_116_, v___x_117_, v___x_118_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v___x_119_, 0);
lean_dec(v_unused_127_);
v___x_121_ = v___x_119_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_dec(v___x_119_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v_a_116_);
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_116_);
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
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
lean_dec(v_a_116_);
v_a_128_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_119_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_119_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
else
{
return v___x_115_;
}
}
else
{
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst___boxed(lean_object* v_c_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v_c_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
lean_dec(v_a_137_);
return v_res_148_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0));
v___x_151_ = l_Lean_stringToMessageData(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2));
v___x_154_ = l_Lean_stringToMessageData(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(lean_object* v_a_155_, lean_object* v_b_156_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1);
v___x_159_ = l_Lean_indentExpr(v_a_155_);
v___x_160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3);
v___x_162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = l_Lean_indentExpr(v_b_156_);
v___x_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___boxed(lean_object* v_a_166_, lean_object* v_b_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_166_, v_b_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(lean_object* v_a_170_, lean_object* v_b_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_170_, v_b_171_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___boxed(lean_object* v_a_178_, lean_object* v_b_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(v_a_178_, v_b_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(lean_object* v_msgData_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; lean_object* v_env_193_; lean_object* v___x_194_; lean_object* v_mctx_195_; lean_object* v_lctx_196_; lean_object* v_options_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_192_ = lean_st_ref_get(v___y_190_);
v_env_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc_ref(v_env_193_);
lean_dec(v___x_192_);
v___x_194_ = lean_st_ref_get(v___y_188_);
v_mctx_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc_ref(v_mctx_195_);
lean_dec(v___x_194_);
v_lctx_196_ = lean_ctor_get(v___y_187_, 2);
v_options_197_ = lean_ctor_get(v___y_189_, 2);
lean_inc_ref(v_options_197_);
lean_inc_ref(v_lctx_196_);
v___x_198_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_198_, 0, v_env_193_);
lean_ctor_set(v___x_198_, 1, v_mctx_195_);
lean_ctor_set(v___x_198_, 2, v_lctx_196_);
lean_ctor_set(v___x_198_, 3, v_options_197_);
v___x_199_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v_msgData_186_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msgData_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(lean_object* v_msg_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_ref_214_; lean_object* v___x_215_; lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_224_; 
v_ref_214_ = lean_ctor_get(v___y_211_, 5);
v___x_215_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_224_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
lean_inc(v_ref_214_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v_ref_214_);
lean_ctor_set(v___x_220_, 1, v_a_216_);
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 1);
lean_ctor_set(v___x_218_, 0, v___x_220_);
v___x_222_ = v___x_218_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg___boxed(lean_object* v_msg_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_msg_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(lean_object* v_a_232_, lean_object* v_b_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_239_; 
lean_inc_ref(v_b_233_);
lean_inc_ref(v_a_232_);
v___x_239_ = l_Lean_Meta_isDefEqD(v_a_232_, v_b_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_252_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_252_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_252_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_252_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
uint8_t v___x_244_; 
v___x_244_ = lean_unbox(v_a_240_);
lean_dec(v_a_240_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v_a_246_; lean_object* v___x_247_; 
lean_del_object(v___x_242_);
v___x_245_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_232_, v_b_233_);
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref(v___x_245_);
v___x_247_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_a_246_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
return v___x_247_;
}
else
{
lean_object* v___x_248_; lean_object* v___x_250_; 
lean_dec_ref(v_b_233_);
lean_dec_ref(v_a_232_);
v___x_248_ = lean_box(0);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_248_);
v___x_250_ = v___x_242_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec_ref(v_b_233_);
lean_dec_ref(v_a_232_);
v_a_253_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_239_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_239_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq___boxed(lean_object* v_a_261_, lean_object* v_b_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_261_, v_b_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(lean_object* v_00_u03b1_269_, lean_object* v_msg_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_msg_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___boxed(lean_object* v_00_u03b1_277_, lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(v_00_u03b1_277_, v_msg_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(lean_object* v_p_285_, lean_object* v_x_286_, size_t v_x_287_, size_t v_x_288_){
_start:
{
if (lean_obj_tag(v_x_286_) == 0)
{
lean_object* v_cs_289_; size_t v_j_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_cs_289_ = lean_ctor_get(v_x_286_, 0);
v_j_290_ = lean_usize_shift_right(v_x_287_, v_x_288_);
v___x_291_ = lean_usize_to_nat(v_j_290_);
v___x_292_ = lean_array_get_size(v_cs_289_);
v___x_293_ = lean_nat_dec_lt(v___x_291_, v___x_292_);
if (v___x_293_ == 0)
{
lean_dec(v___x_291_);
lean_dec(v_p_285_);
return v_x_286_;
}
else
{
lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_311_; 
lean_inc_ref(v_cs_289_);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_286_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; 
v_unused_312_ = lean_ctor_get(v_x_286_, 0);
lean_dec(v_unused_312_);
v___x_295_ = v_x_286_;
v_isShared_296_ = v_isSharedCheck_311_;
goto v_resetjp_294_;
}
else
{
lean_dec(v_x_286_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_311_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v_i_300_; size_t v___x_301_; size_t v_shift_302_; lean_object* v_v_303_; lean_object* v___x_304_; lean_object* v_xs_x27_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_shift_left(v___x_297_, v_x_288_);
v___x_299_ = lean_usize_sub(v___x_298_, v___x_297_);
v_i_300_ = lean_usize_land(v_x_287_, v___x_299_);
v___x_301_ = ((size_t)5ULL);
v_shift_302_ = lean_usize_sub(v_x_288_, v___x_301_);
v_v_303_ = lean_array_fget(v_cs_289_, v___x_291_);
v___x_304_ = lean_box(0);
v_xs_x27_305_ = lean_array_fset(v_cs_289_, v___x_291_, v___x_304_);
v___x_306_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(v_p_285_, v_v_303_, v_i_300_, v_shift_302_);
v___x_307_ = lean_array_fset(v_xs_x27_305_, v___x_291_, v___x_306_);
lean_dec(v___x_291_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_307_);
v___x_309_ = v___x_295_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
else
{
lean_object* v_vs_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_vs_313_ = lean_ctor_get(v_x_286_, 0);
v___x_314_ = lean_usize_to_nat(v_x_287_);
v___x_315_ = lean_array_get_size(v_vs_313_);
v___x_316_ = lean_nat_dec_lt(v___x_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_dec(v___x_314_);
lean_dec(v_p_285_);
return v_x_286_;
}
else
{
lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_330_; 
lean_inc_ref(v_vs_313_);
v_isSharedCheck_330_ = !lean_is_exclusive(v_x_286_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v_x_286_, 0);
lean_dec(v_unused_331_);
v___x_318_ = v_x_286_;
v_isShared_319_ = v_isSharedCheck_330_;
goto v_resetjp_317_;
}
else
{
lean_dec(v_x_286_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_330_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_v_320_; lean_object* v___x_321_; lean_object* v_xs_x27_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v_v_320_ = lean_array_fget(v_vs_313_, v___x_314_);
v___x_321_ = lean_box(0);
v_xs_x27_322_ = lean_array_fset(v_vs_313_, v___x_314_, v___x_321_);
v___x_323_ = lean_box(9);
v___x_324_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_324_, 0, v_p_285_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*2, v___x_316_);
v___x_325_ = l_Lean_PersistentArray_push___redArg(v_v_320_, v___x_324_);
v___x_326_ = lean_array_fset(v_xs_x27_322_, v___x_314_, v___x_325_);
lean_dec(v___x_314_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_326_);
v___x_328_ = v___x_318_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg___boxed(lean_object* v_p_332_, lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
size_t v_x_277__boxed_336_; size_t v_x_278__boxed_337_; lean_object* v_res_338_; 
v_x_277__boxed_336_ = lean_unbox_usize(v_x_334_);
lean_dec(v_x_334_);
v_x_278__boxed_337_ = lean_unbox_usize(v_x_335_);
lean_dec(v_x_335_);
v_res_338_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(v_p_332_, v_x_333_, v_x_277__boxed_336_, v_x_278__boxed_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(lean_object* v_p_339_, lean_object* v_inst_340_, lean_object* v_t_341_, lean_object* v_i_342_){
_start:
{
lean_object* v_root_343_; lean_object* v_tail_344_; lean_object* v_size_345_; size_t v_shift_346_; lean_object* v_tailOff_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_373_; 
v_root_343_ = lean_ctor_get(v_t_341_, 0);
v_tail_344_ = lean_ctor_get(v_t_341_, 1);
v_size_345_ = lean_ctor_get(v_t_341_, 2);
v_shift_346_ = lean_ctor_get_usize(v_t_341_, 4);
v_tailOff_347_ = lean_ctor_get(v_t_341_, 3);
v_isSharedCheck_373_ = !lean_is_exclusive(v_t_341_);
if (v_isSharedCheck_373_ == 0)
{
v___x_349_ = v_t_341_;
v_isShared_350_ = v_isSharedCheck_373_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_tailOff_347_);
lean_inc(v_size_345_);
lean_inc(v_tail_344_);
lean_inc(v_root_343_);
lean_dec(v_t_341_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_373_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
uint8_t v___x_351_; 
v___x_351_ = lean_nat_dec_le(v_tailOff_347_, v_i_342_);
if (v___x_351_ == 0)
{
size_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_352_ = lean_usize_of_nat(v_i_342_);
v___x_353_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(v_p_339_, v_root_343_, v___x_352_, v_shift_346_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_353_);
v___x_355_ = v___x_349_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_tail_344_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_size_345_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_tailOff_347_);
lean_ctor_set_usize(v_reuseFailAlloc_356_, 4, v_shift_346_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_nat_sub(v_i_342_, v_tailOff_347_);
v___x_358_ = lean_array_get_size(v_tail_344_);
v___x_359_ = lean_nat_dec_lt(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_361_; 
lean_dec(v___x_357_);
lean_dec(v_p_339_);
if (v_isShared_350_ == 0)
{
v___x_361_ = v___x_349_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_root_343_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_tail_344_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_size_345_);
lean_ctor_set(v_reuseFailAlloc_362_, 3, v_tailOff_347_);
lean_ctor_set_usize(v_reuseFailAlloc_362_, 4, v_shift_346_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
else
{
lean_object* v_v_363_; lean_object* v___x_364_; lean_object* v_xs_x27_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v_v_363_ = lean_array_fget(v_tail_344_, v___x_357_);
v___x_364_ = lean_box(0);
v_xs_x27_365_ = lean_array_fset(v_tail_344_, v___x_357_, v___x_364_);
v___x_366_ = lean_box(9);
v___x_367_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_367_, 0, v_p_339_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*2, v___x_359_);
v___x_368_ = l_Lean_PersistentArray_push___redArg(v_v_363_, v___x_367_);
v___x_369_ = lean_array_fset(v_xs_x27_365_, v___x_357_, v___x_368_);
lean_dec(v___x_357_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v___x_369_);
v___x_371_ = v___x_349_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_root_343_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_size_345_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_tailOff_347_);
lean_ctor_set_usize(v_reuseFailAlloc_372_, 4, v_shift_346_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0___boxed(lean_object* v_p_374_, lean_object* v_inst_375_, lean_object* v_t_376_, lean_object* v_i_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(v_p_374_, v_inst_375_, v_t_376_, v_i_377_);
lean_dec(v_i_377_);
lean_dec_ref(v_inst_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(lean_object* v_a_379_, lean_object* v_p_380_, lean_object* v___x_381_, lean_object* v_one_382_, lean_object* v_s_383_){
_start:
{
lean_object* v_structs_384_; lean_object* v_typeIdOf_385_; lean_object* v_exprToStructId_386_; lean_object* v_exprToStructIdEntries_387_; lean_object* v_forbiddenNatModules_388_; lean_object* v_natStructs_389_; lean_object* v_natTypeIdOf_390_; lean_object* v_exprToNatStructId_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_structs_384_ = lean_ctor_get(v_s_383_, 0);
v_typeIdOf_385_ = lean_ctor_get(v_s_383_, 1);
v_exprToStructId_386_ = lean_ctor_get(v_s_383_, 2);
v_exprToStructIdEntries_387_ = lean_ctor_get(v_s_383_, 3);
v_forbiddenNatModules_388_ = lean_ctor_get(v_s_383_, 4);
v_natStructs_389_ = lean_ctor_get(v_s_383_, 5);
v_natTypeIdOf_390_ = lean_ctor_get(v_s_383_, 6);
v_exprToNatStructId_391_ = lean_ctor_get(v_s_383_, 7);
v___x_392_ = lean_array_get_size(v_structs_384_);
v___x_393_ = lean_nat_dec_lt(v_a_379_, v___x_392_);
if (v___x_393_ == 0)
{
lean_dec(v_p_380_);
return v_s_383_;
}
else
{
lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_455_; 
lean_inc_ref(v_exprToNatStructId_391_);
lean_inc_ref(v_natTypeIdOf_390_);
lean_inc_ref(v_natStructs_389_);
lean_inc_ref(v_forbiddenNatModules_388_);
lean_inc_ref(v_exprToStructIdEntries_387_);
lean_inc_ref(v_exprToStructId_386_);
lean_inc_ref(v_typeIdOf_385_);
lean_inc_ref(v_structs_384_);
v_isSharedCheck_455_ = !lean_is_exclusive(v_s_383_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; lean_object* v_unused_457_; lean_object* v_unused_458_; lean_object* v_unused_459_; lean_object* v_unused_460_; lean_object* v_unused_461_; lean_object* v_unused_462_; lean_object* v_unused_463_; 
v_unused_456_ = lean_ctor_get(v_s_383_, 7);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_s_383_, 6);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_s_383_, 5);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_s_383_, 4);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_s_383_, 3);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_s_383_, 2);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v_s_383_, 1);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_s_383_, 0);
lean_dec(v_unused_463_);
v___x_395_ = v_s_383_;
v_isShared_396_ = v_isSharedCheck_455_;
goto v_resetjp_394_;
}
else
{
lean_dec(v_s_383_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_455_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_v_397_; lean_object* v_id_398_; lean_object* v_ringId_x3f_399_; lean_object* v_type_400_; lean_object* v_u_401_; lean_object* v_intModuleInst_402_; lean_object* v_leInst_x3f_403_; lean_object* v_ltInst_x3f_404_; lean_object* v_lawfulOrderLTInst_x3f_405_; lean_object* v_isPreorderInst_x3f_406_; lean_object* v_orderedAddInst_x3f_407_; lean_object* v_isLinearInst_x3f_408_; lean_object* v_noNatDivInst_x3f_409_; lean_object* v_ringInst_x3f_410_; lean_object* v_commRingInst_x3f_411_; lean_object* v_orderedRingInst_x3f_412_; lean_object* v_fieldInst_x3f_413_; lean_object* v_charInst_x3f_414_; lean_object* v_zero_415_; lean_object* v_ofNatZero_416_; lean_object* v_one_x3f_417_; lean_object* v_leFn_x3f_418_; lean_object* v_ltFn_x3f_419_; lean_object* v_addFn_420_; lean_object* v_zsmulFn_421_; lean_object* v_nsmulFn_422_; lean_object* v_zsmulFn_x3f_423_; lean_object* v_nsmulFn_x3f_424_; lean_object* v_homomulFn_x3f_425_; lean_object* v_subFn_426_; lean_object* v_negFn_427_; lean_object* v_vars_428_; lean_object* v_varMap_429_; lean_object* v_lowers_430_; lean_object* v_uppers_431_; lean_object* v_diseqs_432_; lean_object* v_assignment_433_; uint8_t v_caseSplits_434_; lean_object* v_conflict_x3f_435_; lean_object* v_diseqSplits_436_; lean_object* v_elimEqs_437_; lean_object* v_elimStack_438_; lean_object* v_occurs_439_; lean_object* v_ignored_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_454_; 
v_v_397_ = lean_array_fget(v_structs_384_, v_a_379_);
v_id_398_ = lean_ctor_get(v_v_397_, 0);
v_ringId_x3f_399_ = lean_ctor_get(v_v_397_, 1);
v_type_400_ = lean_ctor_get(v_v_397_, 2);
v_u_401_ = lean_ctor_get(v_v_397_, 3);
v_intModuleInst_402_ = lean_ctor_get(v_v_397_, 4);
v_leInst_x3f_403_ = lean_ctor_get(v_v_397_, 5);
v_ltInst_x3f_404_ = lean_ctor_get(v_v_397_, 6);
v_lawfulOrderLTInst_x3f_405_ = lean_ctor_get(v_v_397_, 7);
v_isPreorderInst_x3f_406_ = lean_ctor_get(v_v_397_, 8);
v_orderedAddInst_x3f_407_ = lean_ctor_get(v_v_397_, 9);
v_isLinearInst_x3f_408_ = lean_ctor_get(v_v_397_, 10);
v_noNatDivInst_x3f_409_ = lean_ctor_get(v_v_397_, 11);
v_ringInst_x3f_410_ = lean_ctor_get(v_v_397_, 12);
v_commRingInst_x3f_411_ = lean_ctor_get(v_v_397_, 13);
v_orderedRingInst_x3f_412_ = lean_ctor_get(v_v_397_, 14);
v_fieldInst_x3f_413_ = lean_ctor_get(v_v_397_, 15);
v_charInst_x3f_414_ = lean_ctor_get(v_v_397_, 16);
v_zero_415_ = lean_ctor_get(v_v_397_, 17);
v_ofNatZero_416_ = lean_ctor_get(v_v_397_, 18);
v_one_x3f_417_ = lean_ctor_get(v_v_397_, 19);
v_leFn_x3f_418_ = lean_ctor_get(v_v_397_, 20);
v_ltFn_x3f_419_ = lean_ctor_get(v_v_397_, 21);
v_addFn_420_ = lean_ctor_get(v_v_397_, 22);
v_zsmulFn_421_ = lean_ctor_get(v_v_397_, 23);
v_nsmulFn_422_ = lean_ctor_get(v_v_397_, 24);
v_zsmulFn_x3f_423_ = lean_ctor_get(v_v_397_, 25);
v_nsmulFn_x3f_424_ = lean_ctor_get(v_v_397_, 26);
v_homomulFn_x3f_425_ = lean_ctor_get(v_v_397_, 27);
v_subFn_426_ = lean_ctor_get(v_v_397_, 28);
v_negFn_427_ = lean_ctor_get(v_v_397_, 29);
v_vars_428_ = lean_ctor_get(v_v_397_, 30);
v_varMap_429_ = lean_ctor_get(v_v_397_, 31);
v_lowers_430_ = lean_ctor_get(v_v_397_, 32);
v_uppers_431_ = lean_ctor_get(v_v_397_, 33);
v_diseqs_432_ = lean_ctor_get(v_v_397_, 34);
v_assignment_433_ = lean_ctor_get(v_v_397_, 35);
v_caseSplits_434_ = lean_ctor_get_uint8(v_v_397_, sizeof(void*)*42);
v_conflict_x3f_435_ = lean_ctor_get(v_v_397_, 36);
v_diseqSplits_436_ = lean_ctor_get(v_v_397_, 37);
v_elimEqs_437_ = lean_ctor_get(v_v_397_, 38);
v_elimStack_438_ = lean_ctor_get(v_v_397_, 39);
v_occurs_439_ = lean_ctor_get(v_v_397_, 40);
v_ignored_440_ = lean_ctor_get(v_v_397_, 41);
v_isSharedCheck_454_ = !lean_is_exclusive(v_v_397_);
if (v_isSharedCheck_454_ == 0)
{
v___x_442_ = v_v_397_;
v_isShared_443_ = v_isSharedCheck_454_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_ignored_440_);
lean_inc(v_occurs_439_);
lean_inc(v_elimStack_438_);
lean_inc(v_elimEqs_437_);
lean_inc(v_diseqSplits_436_);
lean_inc(v_conflict_x3f_435_);
lean_inc(v_assignment_433_);
lean_inc(v_diseqs_432_);
lean_inc(v_uppers_431_);
lean_inc(v_lowers_430_);
lean_inc(v_varMap_429_);
lean_inc(v_vars_428_);
lean_inc(v_negFn_427_);
lean_inc(v_subFn_426_);
lean_inc(v_homomulFn_x3f_425_);
lean_inc(v_nsmulFn_x3f_424_);
lean_inc(v_zsmulFn_x3f_423_);
lean_inc(v_nsmulFn_422_);
lean_inc(v_zsmulFn_421_);
lean_inc(v_addFn_420_);
lean_inc(v_ltFn_x3f_419_);
lean_inc(v_leFn_x3f_418_);
lean_inc(v_one_x3f_417_);
lean_inc(v_ofNatZero_416_);
lean_inc(v_zero_415_);
lean_inc(v_charInst_x3f_414_);
lean_inc(v_fieldInst_x3f_413_);
lean_inc(v_orderedRingInst_x3f_412_);
lean_inc(v_commRingInst_x3f_411_);
lean_inc(v_ringInst_x3f_410_);
lean_inc(v_noNatDivInst_x3f_409_);
lean_inc(v_isLinearInst_x3f_408_);
lean_inc(v_orderedAddInst_x3f_407_);
lean_inc(v_isPreorderInst_x3f_406_);
lean_inc(v_lawfulOrderLTInst_x3f_405_);
lean_inc(v_ltInst_x3f_404_);
lean_inc(v_leInst_x3f_403_);
lean_inc(v_intModuleInst_402_);
lean_inc(v_u_401_);
lean_inc(v_type_400_);
lean_inc(v_ringId_x3f_399_);
lean_inc(v_id_398_);
lean_dec(v_v_397_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_454_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v_xs_x27_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_444_ = lean_box(0);
v_xs_x27_445_ = lean_array_fset(v_structs_384_, v_a_379_, v___x_444_);
v___x_446_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(v_p_380_, v___x_381_, v_lowers_430_, v_one_382_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 32, v___x_446_);
v___x_448_ = v___x_442_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_id_398_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_ringId_x3f_399_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_type_400_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_u_401_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_intModuleInst_402_);
lean_ctor_set(v_reuseFailAlloc_453_, 5, v_leInst_x3f_403_);
lean_ctor_set(v_reuseFailAlloc_453_, 6, v_ltInst_x3f_404_);
lean_ctor_set(v_reuseFailAlloc_453_, 7, v_lawfulOrderLTInst_x3f_405_);
lean_ctor_set(v_reuseFailAlloc_453_, 8, v_isPreorderInst_x3f_406_);
lean_ctor_set(v_reuseFailAlloc_453_, 9, v_orderedAddInst_x3f_407_);
lean_ctor_set(v_reuseFailAlloc_453_, 10, v_isLinearInst_x3f_408_);
lean_ctor_set(v_reuseFailAlloc_453_, 11, v_noNatDivInst_x3f_409_);
lean_ctor_set(v_reuseFailAlloc_453_, 12, v_ringInst_x3f_410_);
lean_ctor_set(v_reuseFailAlloc_453_, 13, v_commRingInst_x3f_411_);
lean_ctor_set(v_reuseFailAlloc_453_, 14, v_orderedRingInst_x3f_412_);
lean_ctor_set(v_reuseFailAlloc_453_, 15, v_fieldInst_x3f_413_);
lean_ctor_set(v_reuseFailAlloc_453_, 16, v_charInst_x3f_414_);
lean_ctor_set(v_reuseFailAlloc_453_, 17, v_zero_415_);
lean_ctor_set(v_reuseFailAlloc_453_, 18, v_ofNatZero_416_);
lean_ctor_set(v_reuseFailAlloc_453_, 19, v_one_x3f_417_);
lean_ctor_set(v_reuseFailAlloc_453_, 20, v_leFn_x3f_418_);
lean_ctor_set(v_reuseFailAlloc_453_, 21, v_ltFn_x3f_419_);
lean_ctor_set(v_reuseFailAlloc_453_, 22, v_addFn_420_);
lean_ctor_set(v_reuseFailAlloc_453_, 23, v_zsmulFn_421_);
lean_ctor_set(v_reuseFailAlloc_453_, 24, v_nsmulFn_422_);
lean_ctor_set(v_reuseFailAlloc_453_, 25, v_zsmulFn_x3f_423_);
lean_ctor_set(v_reuseFailAlloc_453_, 26, v_nsmulFn_x3f_424_);
lean_ctor_set(v_reuseFailAlloc_453_, 27, v_homomulFn_x3f_425_);
lean_ctor_set(v_reuseFailAlloc_453_, 28, v_subFn_426_);
lean_ctor_set(v_reuseFailAlloc_453_, 29, v_negFn_427_);
lean_ctor_set(v_reuseFailAlloc_453_, 30, v_vars_428_);
lean_ctor_set(v_reuseFailAlloc_453_, 31, v_varMap_429_);
lean_ctor_set(v_reuseFailAlloc_453_, 32, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_453_, 33, v_uppers_431_);
lean_ctor_set(v_reuseFailAlloc_453_, 34, v_diseqs_432_);
lean_ctor_set(v_reuseFailAlloc_453_, 35, v_assignment_433_);
lean_ctor_set(v_reuseFailAlloc_453_, 36, v_conflict_x3f_435_);
lean_ctor_set(v_reuseFailAlloc_453_, 37, v_diseqSplits_436_);
lean_ctor_set(v_reuseFailAlloc_453_, 38, v_elimEqs_437_);
lean_ctor_set(v_reuseFailAlloc_453_, 39, v_elimStack_438_);
lean_ctor_set(v_reuseFailAlloc_453_, 40, v_occurs_439_);
lean_ctor_set(v_reuseFailAlloc_453_, 41, v_ignored_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_453_, sizeof(void*)*42, v_caseSplits_434_);
v___x_448_ = v_reuseFailAlloc_453_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = lean_array_fset(v_xs_x27_445_, v_a_379_, v___x_448_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_449_);
v___x_451_ = v___x_395_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_typeIdOf_385_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_exprToStructId_386_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_exprToStructIdEntries_387_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_forbiddenNatModules_388_);
lean_ctor_set(v_reuseFailAlloc_452_, 5, v_natStructs_389_);
lean_ctor_set(v_reuseFailAlloc_452_, 6, v_natTypeIdOf_390_);
lean_ctor_set(v_reuseFailAlloc_452_, 7, v_exprToNatStructId_391_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed(lean_object* v_a_464_, lean_object* v_p_465_, lean_object* v___x_466_, lean_object* v_one_467_, lean_object* v_s_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(v_a_464_, v_p_465_, v___x_466_, v_one_467_, v_s_468_);
lean_dec(v_one_467_);
lean_dec_ref(v___x_466_);
lean_dec(v_a_464_);
return v_res_469_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_to_int(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1);
v___x_474_ = lean_int_neg(v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(lean_object* v_one_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_p_482_; lean_object* v___f_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_479_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0);
v___x_480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__2);
v___x_481_ = lean_box(0);
lean_inc(v_one_475_);
v_p_482_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_p_482_, 0, v___x_480_);
lean_ctor_set(v_p_482_, 1, v_one_475_);
lean_ctor_set(v_p_482_, 2, v___x_481_);
lean_inc(v_a_476_);
v___f_483_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_483_, 0, v_a_476_);
lean_closure_set(v___f_483_, 1, v_p_482_);
lean_closure_set(v___f_483_, 2, v___x_479_);
lean_closure_set(v___f_483_, 3, v_one_475_);
v___x_484_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_485_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_484_, v___f_483_, v_a_477_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___boxed(lean_object* v_one_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_one_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec(v_a_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(lean_object* v_one_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_one_491_, v_a_492_, v_a_493_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___boxed(lean_object* v_one_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(v_one_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
lean_dec(v_a_507_);
lean_dec(v_a_506_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(lean_object* v_p_519_, lean_object* v_inst_520_, lean_object* v_x_521_, size_t v_x_522_, size_t v_x_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___redArg(v_p_519_, v_x_521_, v_x_522_, v_x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___boxed(lean_object* v_p_525_, lean_object* v_inst_526_, lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
size_t v_x_502__boxed_530_; size_t v_x_503__boxed_531_; lean_object* v_res_532_; 
v_x_502__boxed_530_ = lean_unbox_usize(v_x_528_);
lean_dec(v_x_528_);
v_x_503__boxed_531_ = lean_unbox_usize(v_x_529_);
lean_dec(v_x_529_);
v_res_532_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_525_, v_inst_526_, v_x_527_, v_x_502__boxed_530_, v_x_503__boxed_531_);
lean_dec_ref(v_inst_526_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(lean_object* v_p_533_, lean_object* v_x_534_, size_t v_x_535_, size_t v_x_536_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
lean_object* v_cs_537_; size_t v_j_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_cs_537_ = lean_ctor_get(v_x_534_, 0);
v_j_538_ = lean_usize_shift_right(v_x_535_, v_x_536_);
v___x_539_ = lean_usize_to_nat(v_j_538_);
v___x_540_ = lean_array_get_size(v_cs_537_);
v___x_541_ = lean_nat_dec_lt(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_dec(v___x_539_);
lean_dec(v_p_533_);
return v_x_534_;
}
else
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_559_; 
lean_inc_ref(v_cs_537_);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_534_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v_x_534_, 0);
lean_dec(v_unused_560_);
v___x_543_ = v_x_534_;
v_isShared_544_ = v_isSharedCheck_559_;
goto v_resetjp_542_;
}
else
{
lean_dec(v_x_534_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_559_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
size_t v___x_545_; size_t v___x_546_; size_t v___x_547_; size_t v_i_548_; size_t v___x_549_; size_t v_shift_550_; lean_object* v_v_551_; lean_object* v___x_552_; lean_object* v_xs_x27_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_545_ = ((size_t)1ULL);
v___x_546_ = lean_usize_shift_left(v___x_545_, v_x_536_);
v___x_547_ = lean_usize_sub(v___x_546_, v___x_545_);
v_i_548_ = lean_usize_land(v_x_535_, v___x_547_);
v___x_549_ = ((size_t)5ULL);
v_shift_550_ = lean_usize_sub(v_x_536_, v___x_549_);
v_v_551_ = lean_array_fget(v_cs_537_, v___x_539_);
v___x_552_ = lean_box(0);
v_xs_x27_553_ = lean_array_fset(v_cs_537_, v___x_539_, v___x_552_);
v___x_554_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(v_p_533_, v_v_551_, v_i_548_, v_shift_550_);
v___x_555_ = lean_array_fset(v_xs_x27_553_, v___x_539_, v___x_554_);
lean_dec(v___x_539_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_555_);
v___x_557_ = v___x_543_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v_vs_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_vs_561_ = lean_ctor_get(v_x_534_, 0);
v___x_562_ = lean_usize_to_nat(v_x_535_);
v___x_563_ = lean_array_get_size(v_vs_561_);
v___x_564_ = lean_nat_dec_lt(v___x_562_, v___x_563_);
if (v___x_564_ == 0)
{
lean_dec(v___x_562_);
lean_dec(v_p_533_);
return v_x_534_;
}
else
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_578_; 
lean_inc_ref(v_vs_561_);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_534_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v_x_534_, 0);
lean_dec(v_unused_579_);
v___x_566_ = v_x_534_;
v_isShared_567_ = v_isSharedCheck_578_;
goto v_resetjp_565_;
}
else
{
lean_dec(v_x_534_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_578_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v_v_568_; lean_object* v___x_569_; lean_object* v_xs_x27_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v_v_568_ = lean_array_fget(v_vs_561_, v___x_562_);
v___x_569_ = lean_box(0);
v_xs_x27_570_ = lean_array_fset(v_vs_561_, v___x_562_, v___x_569_);
v___x_571_ = lean_box(6);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_p_533_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Lean_PersistentArray_push___redArg(v_v_568_, v___x_572_);
v___x_574_ = lean_array_fset(v_xs_x27_570_, v___x_562_, v___x_573_);
lean_dec(v___x_562_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_574_);
v___x_576_ = v___x_566_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg___boxed(lean_object* v_p_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
size_t v_x_266__boxed_584_; size_t v_x_267__boxed_585_; lean_object* v_res_586_; 
v_x_266__boxed_584_ = lean_unbox_usize(v_x_582_);
lean_dec(v_x_582_);
v_x_267__boxed_585_ = lean_unbox_usize(v_x_583_);
lean_dec(v_x_583_);
v_res_586_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(v_p_580_, v_x_581_, v_x_266__boxed_584_, v_x_267__boxed_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(lean_object* v_p_587_, lean_object* v_inst_588_, lean_object* v_t_589_, lean_object* v_i_590_){
_start:
{
lean_object* v_root_591_; lean_object* v_tail_592_; lean_object* v_size_593_; size_t v_shift_594_; lean_object* v_tailOff_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_621_; 
v_root_591_ = lean_ctor_get(v_t_589_, 0);
v_tail_592_ = lean_ctor_get(v_t_589_, 1);
v_size_593_ = lean_ctor_get(v_t_589_, 2);
v_shift_594_ = lean_ctor_get_usize(v_t_589_, 4);
v_tailOff_595_ = lean_ctor_get(v_t_589_, 3);
v_isSharedCheck_621_ = !lean_is_exclusive(v_t_589_);
if (v_isSharedCheck_621_ == 0)
{
v___x_597_ = v_t_589_;
v_isShared_598_ = v_isSharedCheck_621_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_tailOff_595_);
lean_inc(v_size_593_);
lean_inc(v_tail_592_);
lean_inc(v_root_591_);
lean_dec(v_t_589_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_621_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
uint8_t v___x_599_; 
v___x_599_ = lean_nat_dec_le(v_tailOff_595_, v_i_590_);
if (v___x_599_ == 0)
{
size_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_600_ = lean_usize_of_nat(v_i_590_);
v___x_601_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(v_p_587_, v_root_591_, v___x_600_, v_shift_594_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_601_);
v___x_603_ = v___x_597_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_tail_592_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_size_593_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_tailOff_595_);
lean_ctor_set_usize(v_reuseFailAlloc_604_, 4, v_shift_594_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = lean_nat_sub(v_i_590_, v_tailOff_595_);
v___x_606_ = lean_array_get_size(v_tail_592_);
v___x_607_ = lean_nat_dec_lt(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_609_; 
lean_dec(v___x_605_);
lean_dec(v_p_587_);
if (v_isShared_598_ == 0)
{
v___x_609_ = v___x_597_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_root_591_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_tail_592_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_size_593_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_tailOff_595_);
lean_ctor_set_usize(v_reuseFailAlloc_610_, 4, v_shift_594_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
lean_object* v_v_611_; lean_object* v___x_612_; lean_object* v_xs_x27_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v_v_611_ = lean_array_fget(v_tail_592_, v___x_605_);
v___x_612_ = lean_box(0);
v_xs_x27_613_ = lean_array_fset(v_tail_592_, v___x_605_, v___x_612_);
v___x_614_ = lean_box(6);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v_p_587_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Lean_PersistentArray_push___redArg(v_v_611_, v___x_615_);
v___x_617_ = lean_array_fset(v_xs_x27_613_, v___x_605_, v___x_616_);
lean_dec(v___x_605_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 1, v___x_617_);
v___x_619_ = v___x_597_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_root_591_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_size_593_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_tailOff_595_);
lean_ctor_set_usize(v_reuseFailAlloc_620_, 4, v_shift_594_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0___boxed(lean_object* v_p_622_, lean_object* v_inst_623_, lean_object* v_t_624_, lean_object* v_i_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(v_p_622_, v_inst_623_, v_t_624_, v_i_625_);
lean_dec(v_i_625_);
lean_dec_ref(v_inst_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(lean_object* v_a_627_, lean_object* v_p_628_, lean_object* v___x_629_, lean_object* v_one_630_, lean_object* v_s_631_){
_start:
{
lean_object* v_structs_632_; lean_object* v_typeIdOf_633_; lean_object* v_exprToStructId_634_; lean_object* v_exprToStructIdEntries_635_; lean_object* v_forbiddenNatModules_636_; lean_object* v_natStructs_637_; lean_object* v_natTypeIdOf_638_; lean_object* v_exprToNatStructId_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_structs_632_ = lean_ctor_get(v_s_631_, 0);
v_typeIdOf_633_ = lean_ctor_get(v_s_631_, 1);
v_exprToStructId_634_ = lean_ctor_get(v_s_631_, 2);
v_exprToStructIdEntries_635_ = lean_ctor_get(v_s_631_, 3);
v_forbiddenNatModules_636_ = lean_ctor_get(v_s_631_, 4);
v_natStructs_637_ = lean_ctor_get(v_s_631_, 5);
v_natTypeIdOf_638_ = lean_ctor_get(v_s_631_, 6);
v_exprToNatStructId_639_ = lean_ctor_get(v_s_631_, 7);
v___x_640_ = lean_array_get_size(v_structs_632_);
v___x_641_ = lean_nat_dec_lt(v_a_627_, v___x_640_);
if (v___x_641_ == 0)
{
lean_dec(v_p_628_);
return v_s_631_;
}
else
{
lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_703_; 
lean_inc_ref(v_exprToNatStructId_639_);
lean_inc_ref(v_natTypeIdOf_638_);
lean_inc_ref(v_natStructs_637_);
lean_inc_ref(v_forbiddenNatModules_636_);
lean_inc_ref(v_exprToStructIdEntries_635_);
lean_inc_ref(v_exprToStructId_634_);
lean_inc_ref(v_typeIdOf_633_);
lean_inc_ref(v_structs_632_);
v_isSharedCheck_703_ = !lean_is_exclusive(v_s_631_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; lean_object* v_unused_705_; lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; 
v_unused_704_ = lean_ctor_get(v_s_631_, 7);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v_s_631_, 6);
lean_dec(v_unused_705_);
v_unused_706_ = lean_ctor_get(v_s_631_, 5);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_s_631_, 4);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_s_631_, 3);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_s_631_, 2);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_s_631_, 1);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_s_631_, 0);
lean_dec(v_unused_711_);
v___x_643_ = v_s_631_;
v_isShared_644_ = v_isSharedCheck_703_;
goto v_resetjp_642_;
}
else
{
lean_dec(v_s_631_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_703_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_v_645_; lean_object* v_id_646_; lean_object* v_ringId_x3f_647_; lean_object* v_type_648_; lean_object* v_u_649_; lean_object* v_intModuleInst_650_; lean_object* v_leInst_x3f_651_; lean_object* v_ltInst_x3f_652_; lean_object* v_lawfulOrderLTInst_x3f_653_; lean_object* v_isPreorderInst_x3f_654_; lean_object* v_orderedAddInst_x3f_655_; lean_object* v_isLinearInst_x3f_656_; lean_object* v_noNatDivInst_x3f_657_; lean_object* v_ringInst_x3f_658_; lean_object* v_commRingInst_x3f_659_; lean_object* v_orderedRingInst_x3f_660_; lean_object* v_fieldInst_x3f_661_; lean_object* v_charInst_x3f_662_; lean_object* v_zero_663_; lean_object* v_ofNatZero_664_; lean_object* v_one_x3f_665_; lean_object* v_leFn_x3f_666_; lean_object* v_ltFn_x3f_667_; lean_object* v_addFn_668_; lean_object* v_zsmulFn_669_; lean_object* v_nsmulFn_670_; lean_object* v_zsmulFn_x3f_671_; lean_object* v_nsmulFn_x3f_672_; lean_object* v_homomulFn_x3f_673_; lean_object* v_subFn_674_; lean_object* v_negFn_675_; lean_object* v_vars_676_; lean_object* v_varMap_677_; lean_object* v_lowers_678_; lean_object* v_uppers_679_; lean_object* v_diseqs_680_; lean_object* v_assignment_681_; uint8_t v_caseSplits_682_; lean_object* v_conflict_x3f_683_; lean_object* v_diseqSplits_684_; lean_object* v_elimEqs_685_; lean_object* v_elimStack_686_; lean_object* v_occurs_687_; lean_object* v_ignored_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_702_; 
v_v_645_ = lean_array_fget(v_structs_632_, v_a_627_);
v_id_646_ = lean_ctor_get(v_v_645_, 0);
v_ringId_x3f_647_ = lean_ctor_get(v_v_645_, 1);
v_type_648_ = lean_ctor_get(v_v_645_, 2);
v_u_649_ = lean_ctor_get(v_v_645_, 3);
v_intModuleInst_650_ = lean_ctor_get(v_v_645_, 4);
v_leInst_x3f_651_ = lean_ctor_get(v_v_645_, 5);
v_ltInst_x3f_652_ = lean_ctor_get(v_v_645_, 6);
v_lawfulOrderLTInst_x3f_653_ = lean_ctor_get(v_v_645_, 7);
v_isPreorderInst_x3f_654_ = lean_ctor_get(v_v_645_, 8);
v_orderedAddInst_x3f_655_ = lean_ctor_get(v_v_645_, 9);
v_isLinearInst_x3f_656_ = lean_ctor_get(v_v_645_, 10);
v_noNatDivInst_x3f_657_ = lean_ctor_get(v_v_645_, 11);
v_ringInst_x3f_658_ = lean_ctor_get(v_v_645_, 12);
v_commRingInst_x3f_659_ = lean_ctor_get(v_v_645_, 13);
v_orderedRingInst_x3f_660_ = lean_ctor_get(v_v_645_, 14);
v_fieldInst_x3f_661_ = lean_ctor_get(v_v_645_, 15);
v_charInst_x3f_662_ = lean_ctor_get(v_v_645_, 16);
v_zero_663_ = lean_ctor_get(v_v_645_, 17);
v_ofNatZero_664_ = lean_ctor_get(v_v_645_, 18);
v_one_x3f_665_ = lean_ctor_get(v_v_645_, 19);
v_leFn_x3f_666_ = lean_ctor_get(v_v_645_, 20);
v_ltFn_x3f_667_ = lean_ctor_get(v_v_645_, 21);
v_addFn_668_ = lean_ctor_get(v_v_645_, 22);
v_zsmulFn_669_ = lean_ctor_get(v_v_645_, 23);
v_nsmulFn_670_ = lean_ctor_get(v_v_645_, 24);
v_zsmulFn_x3f_671_ = lean_ctor_get(v_v_645_, 25);
v_nsmulFn_x3f_672_ = lean_ctor_get(v_v_645_, 26);
v_homomulFn_x3f_673_ = lean_ctor_get(v_v_645_, 27);
v_subFn_674_ = lean_ctor_get(v_v_645_, 28);
v_negFn_675_ = lean_ctor_get(v_v_645_, 29);
v_vars_676_ = lean_ctor_get(v_v_645_, 30);
v_varMap_677_ = lean_ctor_get(v_v_645_, 31);
v_lowers_678_ = lean_ctor_get(v_v_645_, 32);
v_uppers_679_ = lean_ctor_get(v_v_645_, 33);
v_diseqs_680_ = lean_ctor_get(v_v_645_, 34);
v_assignment_681_ = lean_ctor_get(v_v_645_, 35);
v_caseSplits_682_ = lean_ctor_get_uint8(v_v_645_, sizeof(void*)*42);
v_conflict_x3f_683_ = lean_ctor_get(v_v_645_, 36);
v_diseqSplits_684_ = lean_ctor_get(v_v_645_, 37);
v_elimEqs_685_ = lean_ctor_get(v_v_645_, 38);
v_elimStack_686_ = lean_ctor_get(v_v_645_, 39);
v_occurs_687_ = lean_ctor_get(v_v_645_, 40);
v_ignored_688_ = lean_ctor_get(v_v_645_, 41);
v_isSharedCheck_702_ = !lean_is_exclusive(v_v_645_);
if (v_isSharedCheck_702_ == 0)
{
v___x_690_ = v_v_645_;
v_isShared_691_ = v_isSharedCheck_702_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_ignored_688_);
lean_inc(v_occurs_687_);
lean_inc(v_elimStack_686_);
lean_inc(v_elimEqs_685_);
lean_inc(v_diseqSplits_684_);
lean_inc(v_conflict_x3f_683_);
lean_inc(v_assignment_681_);
lean_inc(v_diseqs_680_);
lean_inc(v_uppers_679_);
lean_inc(v_lowers_678_);
lean_inc(v_varMap_677_);
lean_inc(v_vars_676_);
lean_inc(v_negFn_675_);
lean_inc(v_subFn_674_);
lean_inc(v_homomulFn_x3f_673_);
lean_inc(v_nsmulFn_x3f_672_);
lean_inc(v_zsmulFn_x3f_671_);
lean_inc(v_nsmulFn_670_);
lean_inc(v_zsmulFn_669_);
lean_inc(v_addFn_668_);
lean_inc(v_ltFn_x3f_667_);
lean_inc(v_leFn_x3f_666_);
lean_inc(v_one_x3f_665_);
lean_inc(v_ofNatZero_664_);
lean_inc(v_zero_663_);
lean_inc(v_charInst_x3f_662_);
lean_inc(v_fieldInst_x3f_661_);
lean_inc(v_orderedRingInst_x3f_660_);
lean_inc(v_commRingInst_x3f_659_);
lean_inc(v_ringInst_x3f_658_);
lean_inc(v_noNatDivInst_x3f_657_);
lean_inc(v_isLinearInst_x3f_656_);
lean_inc(v_orderedAddInst_x3f_655_);
lean_inc(v_isPreorderInst_x3f_654_);
lean_inc(v_lawfulOrderLTInst_x3f_653_);
lean_inc(v_ltInst_x3f_652_);
lean_inc(v_leInst_x3f_651_);
lean_inc(v_intModuleInst_650_);
lean_inc(v_u_649_);
lean_inc(v_type_648_);
lean_inc(v_ringId_x3f_647_);
lean_inc(v_id_646_);
lean_dec(v_v_645_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_702_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v_xs_x27_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_692_ = lean_box(0);
v_xs_x27_693_ = lean_array_fset(v_structs_632_, v_a_627_, v___x_692_);
v___x_694_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(v_p_628_, v___x_629_, v_diseqs_680_, v_one_630_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 34, v___x_694_);
v___x_696_ = v___x_690_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_id_646_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_ringId_x3f_647_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_type_648_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_u_649_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_intModuleInst_650_);
lean_ctor_set(v_reuseFailAlloc_701_, 5, v_leInst_x3f_651_);
lean_ctor_set(v_reuseFailAlloc_701_, 6, v_ltInst_x3f_652_);
lean_ctor_set(v_reuseFailAlloc_701_, 7, v_lawfulOrderLTInst_x3f_653_);
lean_ctor_set(v_reuseFailAlloc_701_, 8, v_isPreorderInst_x3f_654_);
lean_ctor_set(v_reuseFailAlloc_701_, 9, v_orderedAddInst_x3f_655_);
lean_ctor_set(v_reuseFailAlloc_701_, 10, v_isLinearInst_x3f_656_);
lean_ctor_set(v_reuseFailAlloc_701_, 11, v_noNatDivInst_x3f_657_);
lean_ctor_set(v_reuseFailAlloc_701_, 12, v_ringInst_x3f_658_);
lean_ctor_set(v_reuseFailAlloc_701_, 13, v_commRingInst_x3f_659_);
lean_ctor_set(v_reuseFailAlloc_701_, 14, v_orderedRingInst_x3f_660_);
lean_ctor_set(v_reuseFailAlloc_701_, 15, v_fieldInst_x3f_661_);
lean_ctor_set(v_reuseFailAlloc_701_, 16, v_charInst_x3f_662_);
lean_ctor_set(v_reuseFailAlloc_701_, 17, v_zero_663_);
lean_ctor_set(v_reuseFailAlloc_701_, 18, v_ofNatZero_664_);
lean_ctor_set(v_reuseFailAlloc_701_, 19, v_one_x3f_665_);
lean_ctor_set(v_reuseFailAlloc_701_, 20, v_leFn_x3f_666_);
lean_ctor_set(v_reuseFailAlloc_701_, 21, v_ltFn_x3f_667_);
lean_ctor_set(v_reuseFailAlloc_701_, 22, v_addFn_668_);
lean_ctor_set(v_reuseFailAlloc_701_, 23, v_zsmulFn_669_);
lean_ctor_set(v_reuseFailAlloc_701_, 24, v_nsmulFn_670_);
lean_ctor_set(v_reuseFailAlloc_701_, 25, v_zsmulFn_x3f_671_);
lean_ctor_set(v_reuseFailAlloc_701_, 26, v_nsmulFn_x3f_672_);
lean_ctor_set(v_reuseFailAlloc_701_, 27, v_homomulFn_x3f_673_);
lean_ctor_set(v_reuseFailAlloc_701_, 28, v_subFn_674_);
lean_ctor_set(v_reuseFailAlloc_701_, 29, v_negFn_675_);
lean_ctor_set(v_reuseFailAlloc_701_, 30, v_vars_676_);
lean_ctor_set(v_reuseFailAlloc_701_, 31, v_varMap_677_);
lean_ctor_set(v_reuseFailAlloc_701_, 32, v_lowers_678_);
lean_ctor_set(v_reuseFailAlloc_701_, 33, v_uppers_679_);
lean_ctor_set(v_reuseFailAlloc_701_, 34, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_701_, 35, v_assignment_681_);
lean_ctor_set(v_reuseFailAlloc_701_, 36, v_conflict_x3f_683_);
lean_ctor_set(v_reuseFailAlloc_701_, 37, v_diseqSplits_684_);
lean_ctor_set(v_reuseFailAlloc_701_, 38, v_elimEqs_685_);
lean_ctor_set(v_reuseFailAlloc_701_, 39, v_elimStack_686_);
lean_ctor_set(v_reuseFailAlloc_701_, 40, v_occurs_687_);
lean_ctor_set(v_reuseFailAlloc_701_, 41, v_ignored_688_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*42, v_caseSplits_682_);
v___x_696_ = v_reuseFailAlloc_701_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_array_fset(v_xs_x27_693_, v_a_627_, v___x_696_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_697_);
v___x_699_ = v___x_643_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_typeIdOf_633_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_exprToStructId_634_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_exprToStructIdEntries_635_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_forbiddenNatModules_636_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v_natStructs_637_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_natTypeIdOf_638_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_exprToNatStructId_639_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed(lean_object* v_a_712_, lean_object* v_p_713_, lean_object* v___x_714_, lean_object* v_one_715_, lean_object* v_s_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(v_a_712_, v_p_713_, v___x_714_, v_one_715_, v_s_716_);
lean_dec(v_one_715_);
lean_dec_ref(v___x_714_);
lean_dec(v_a_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(lean_object* v_one_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v_p_725_; lean_object* v___f_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_722_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0);
v___x_723_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1);
v___x_724_ = lean_box(0);
lean_inc(v_one_718_);
v_p_725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_p_725_, 0, v___x_723_);
lean_ctor_set(v_p_725_, 1, v_one_718_);
lean_ctor_set(v_p_725_, 2, v___x_724_);
lean_inc(v_a_719_);
v___f_726_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_726_, 0, v_a_719_);
lean_closure_set(v___f_726_, 1, v_p_725_);
lean_closure_set(v___f_726_, 2, v___x_722_);
lean_closure_set(v___f_726_, 3, v_one_718_);
v___x_727_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_728_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_727_, v___f_726_, v_a_720_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___boxed(lean_object* v_one_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_one_729_, v_a_730_, v_a_731_);
lean_dec(v_a_731_);
lean_dec(v_a_730_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(lean_object* v_one_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_one_734_, v_a_735_, v_a_736_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___boxed(lean_object* v_one_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(v_one_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec(v_a_750_);
lean_dec(v_a_749_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(lean_object* v_p_762_, lean_object* v_inst_763_, lean_object* v_x_764_, size_t v_x_765_, size_t v_x_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___redArg(v_p_762_, v_x_764_, v_x_765_, v_x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___boxed(lean_object* v_p_768_, lean_object* v_inst_769_, lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
size_t v_x_480__boxed_773_; size_t v_x_481__boxed_774_; lean_object* v_res_775_; 
v_x_480__boxed_773_ = lean_unbox_usize(v_x_771_);
lean_dec(v_x_771_);
v_x_481__boxed_774_ = lean_unbox_usize(v_x_772_);
lean_dec(v_x_772_);
v_res_775_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_768_, v_inst_769_, v_x_770_, v_x_480__boxed_773_, v_x_481__boxed_774_);
lean_dec_ref(v_inst_769_);
return v_res_775_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(lean_object* v_isCharInst_x3f_776_){
_start:
{
if (lean_obj_tag(v_isCharInst_x3f_776_) == 0)
{
uint8_t v___x_777_; 
v___x_777_ = 0;
return v___x_777_;
}
else
{
lean_object* v_val_778_; lean_object* v_snd_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_val_778_ = lean_ctor_get(v_isCharInst_x3f_776_, 0);
v_snd_779_ = lean_ctor_get(v_val_778_, 1);
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_dec_eq(v_snd_779_, v___x_780_);
if (v___x_781_ == 0)
{
uint8_t v___x_782_; 
v___x_782_ = 1;
return v___x_782_;
}
else
{
uint8_t v___x_783_; 
v___x_783_ = 0;
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst___boxed(lean_object* v_isCharInst_x3f_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v_isCharInst_x3f_784_);
lean_dec(v_isCharInst_x3f_784_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(lean_object* v_type_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_790_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; uint8_t v_lia_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref(v___x_803_);
v_lia_805_ = lean_ctor_get_uint8(v_a_804_, sizeof(void*)*11 + 23);
lean_dec(v_a_804_);
if (v_lia_805_ == 0)
{
lean_dec_ref(v_type_787_);
goto v___jp_799_;
}
else
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(v_type_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; uint8_t v___x_808_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
v___x_808_ = lean_unbox(v_a_807_);
lean_dec(v_a_807_);
if (v___x_808_ == 0)
{
lean_dec_ref(v___x_806_);
goto v___jp_799_;
}
else
{
return v___x_806_;
}
}
else
{
return v___x_806_;
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_type_787_);
v_a_809_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_803_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_803_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
v___jp_799_:
{
uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = 0;
v___x_801_ = lean_box(v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___boxed(lean_object* v_type_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
lean_dec(v_a_819_);
lean_dec(v_a_818_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(lean_object* v_ringId_x3f_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_830_) == 1)
{
lean_object* v_val_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_869_; 
v_val_842_ = lean_ctor_get(v_ringId_x3f_830_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_ringId_x3f_830_);
if (v_isSharedCheck_869_ == 0)
{
v___x_844_ = v_ringId_x3f_830_;
v_isShared_845_ = v_isSharedCheck_869_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_val_842_);
lean_dec(v_ringId_x3f_830_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_869_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = 0;
v___x_847_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_847_, 0, v_val_842_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*1, v___x_846_);
v___x_848_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_847_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
lean_dec_ref(v___x_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_860_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_860_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_860_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_860_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_commRingInst_853_; lean_object* v___x_855_; 
v_commRingInst_853_ = lean_ctor_get(v_a_849_, 4);
lean_inc_ref(v_commRingInst_853_);
lean_dec(v_a_849_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v_commRingInst_853_);
v___x_855_ = v___x_844_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_commRingInst_853_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_855_);
v___x_857_ = v___x_851_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_del_object(v___x_844_);
v_a_861_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_848_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_848_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec(v_ringId_x3f_830_);
v___x_870_ = lean_box(0);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f___boxed(lean_object* v_ringId_x3f_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_ringId_x3f_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec(v_a_873_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object* v_u_899_, lean_object* v_type_900_, lean_object* v_commRingInst_x3f_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
if (lean_obj_tag(v_commRingInst_x3f_901_) == 1)
{
lean_object* v_val_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_920_; 
v_val_907_ = lean_ctor_get(v_commRingInst_x3f_901_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v_commRingInst_x3f_901_);
if (v_isSharedCheck_920_ == 0)
{
v___x_909_ = v_commRingInst_x3f_901_;
v_isShared_910_ = v_isSharedCheck_920_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_val_907_);
lean_dec(v_commRingInst_x3f_901_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_920_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4));
v___x_912_ = lean_box(0);
v___x_913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_913_, 0, v_u_899_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Lean_mkConst(v___x_911_, v___x_913_);
v___x_915_ = l_Lean_mkAppB(v___x_914_, v_type_900_, v_val_907_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_915_);
v___x_917_ = v___x_909_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_919_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; 
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v_commRingInst_x3f_901_);
v___x_921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6));
v___x_922_ = lean_box(0);
v___x_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_923_, 0, v_u_899_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = l_Lean_mkConst(v___x_921_, v___x_923_);
v___x_925_ = l_Lean_Expr_app___override(v___x_924_, v_type_900_);
v___x_926_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_925_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
return v___x_926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object* v_u_927_, lean_object* v_type_928_, lean_object* v_commRingInst_x3f_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_927_, v_type_928_, v_commRingInst_x3f_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object* v_u_936_, lean_object* v_type_937_, lean_object* v_commRingInst_x3f_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_936_, v_type_937_, v_commRingInst_x3f_938_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object* v_u_951_, lean_object* v_type_952_, lean_object* v_commRingInst_x3f_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(v_u_951_, v_type_952_, v_commRingInst_x3f_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec(v_a_954_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object* v_u_977_, lean_object* v_type_978_, lean_object* v_ringInst_x3f_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_979_) == 1)
{
lean_object* v_val_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_998_; 
v_val_985_ = lean_ctor_get(v_ringInst_x3f_979_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v_ringInst_x3f_979_);
if (v_isSharedCheck_998_ == 0)
{
v___x_987_ = v_ringInst_x3f_979_;
v_isShared_988_ = v_isSharedCheck_998_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_val_985_);
lean_dec(v_ringInst_x3f_979_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_998_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1));
v___x_990_ = lean_box(0);
v___x_991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_991_, 0, v_u_977_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l_Lean_mkConst(v___x_989_, v___x_991_);
v___x_993_ = l_Lean_mkAppB(v___x_992_, v_type_978_, v_val_985_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_993_);
v___x_995_ = v___x_987_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_997_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; 
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec(v_ringInst_x3f_979_);
v___x_999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_u_977_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_mkConst(v___x_999_, v___x_1001_);
v___x_1003_ = l_Lean_Expr_app___override(v___x_1002_, v_type_978_);
v___x_1004_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_1003_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object* v_u_1005_, lean_object* v_type_1006_, lean_object* v_ringInst_x3f_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1005_, v_type_1006_, v_ringInst_x3f_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object* v_u_1014_, lean_object* v_type_1015_, lean_object* v_ringInst_x3f_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1014_, v_type_1015_, v_ringInst_x3f_1016_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object* v_u_1029_, lean_object* v_type_1030_, lean_object* v_ringInst_x3f_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(v_u_1029_, v_type_1030_, v_ringInst_x3f_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec(v_a_1032_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object* v_u_1055_, lean_object* v_type_1056_, lean_object* v_ringInst_x3f_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1057_) == 1)
{
lean_object* v_val_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1076_; 
v_val_1063_ = lean_ctor_get(v_ringInst_x3f_1057_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_ringInst_x3f_1057_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1065_ = v_ringInst_x3f_1057_;
v_isShared_1066_ = v_isSharedCheck_1076_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_val_1063_);
lean_dec(v_ringInst_x3f_1057_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1076_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1));
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1069_, 0, v_u_1055_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_mkConst(v___x_1067_, v___x_1069_);
v___x_1071_ = l_Lean_mkAppB(v___x_1070_, v_type_1056_, v_val_1063_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1071_);
v___x_1073_ = v___x_1065_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec(v_ringInst_x3f_1057_);
v___x_1077_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3));
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1079_, 0, v_u_1055_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = l_Lean_mkConst(v___x_1077_, v___x_1079_);
v___x_1081_ = l_Lean_Expr_app___override(v___x_1080_, v_type_1056_);
v___x_1082_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_1081_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object* v_u_1083_, lean_object* v_type_1084_, lean_object* v_ringInst_x3f_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1083_, v_type_1084_, v_ringInst_x3f_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object* v_u_1092_, lean_object* v_type_1093_, lean_object* v_ringInst_x3f_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1092_, v_type_1093_, v_ringInst_x3f_1094_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object* v_u_1107_, lean_object* v_type_1108_, lean_object* v_ringInst_x3f_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(v_u_1107_, v_type_1108_, v_ringInst_x3f_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec(v_a_1110_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object* v_u_1129_, lean_object* v_type_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1));
v___x_1143_ = lean_box(0);
v___x_1144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_u_1129_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
lean_inc_ref(v___x_1144_);
v___x_1145_ = l_Lean_mkConst(v___x_1142_, v___x_1144_);
lean_inc_ref(v_type_1130_);
v___x_1146_ = l_Lean_Expr_app___override(v___x_1145_, v_type_1130_);
v___x_1147_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_1146_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1229_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1229_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1229_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
if (lean_obj_tag(v_a_1148_) == 1)
{
lean_object* v_val_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1224_; 
lean_del_object(v___x_1150_);
v_val_1152_ = lean_ctor_get(v_a_1148_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_a_1148_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1154_ = v_a_1148_;
v_isShared_1155_ = v_isSharedCheck_1224_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_val_1152_);
lean_dec(v_a_1148_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1224_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3));
v___x_1157_ = l_Lean_mkConst(v___x_1156_, v___x_1144_);
lean_inc_ref(v_type_1130_);
v___x_1158_ = l_Lean_mkAppB(v___x_1157_, v_type_1130_, v_val_1152_);
v___x_1159_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_1158_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1215_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1215_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1215_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_unsigned_to_nat(1u);
v___x_1172_ = l_Lean_Meta_mkNumeral(v_type_1130_, v___x_1171_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref(v___x_1172_);
lean_inc(v_a_1173_);
lean_inc(v_a_1160_);
v___x_1174_ = l_Lean_Meta_isDefEqD(v_a_1160_, v_a_1173_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; uint8_t v___x_1176_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___x_1174_);
v___x_1176_ = lean_unbox(v_a_1175_);
lean_dec(v_a_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v_a_1178_; lean_object* v___x_1179_; 
lean_inc(v_a_1160_);
v___x_1177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_1160_, v_a_1173_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v___x_1177_);
v___x_1179_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1135_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; uint8_t v___x_1181_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref(v___x_1179_);
v___x_1181_ = lean_unbox(v_a_1180_);
lean_dec(v_a_1180_);
if (v___x_1181_ == 0)
{
lean_dec(v_a_1178_);
goto v___jp_1164_;
}
else
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_Meta_Sym_reportIssue(v_a_1178_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_dec_ref(v___x_1182_);
goto v___jp_1164_;
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_del_object(v___x_1162_);
lean_dec(v_a_1160_);
lean_del_object(v___x_1154_);
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_a_1178_);
lean_del_object(v___x_1162_);
lean_dec(v_a_1160_);
lean_del_object(v___x_1154_);
v_a_1191_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1179_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1179_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_dec(v_a_1173_);
goto v___jp_1164_;
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v_a_1173_);
lean_del_object(v___x_1162_);
lean_dec(v_a_1160_);
lean_del_object(v___x_1154_);
v_a_1199_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1174_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1174_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_del_object(v___x_1162_);
lean_dec(v_a_1160_);
lean_del_object(v___x_1154_);
v_a_1207_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1172_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1172_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
v___jp_1164_:
{
lean_object* v___x_1166_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v_a_1160_);
v___x_1166_ = v___x_1154_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1160_);
v___x_1166_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1166_);
v___x_1168_ = v___x_1162_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_del_object(v___x_1154_);
lean_dec_ref(v_type_1130_);
v_a_1216_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1159_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1159_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
lean_dec(v_a_1148_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_type_1130_);
v___x_1225_ = lean_box(0);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1225_);
v___x_1227_ = v___x_1150_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
else
{
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_type_1130_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object* v_u_1230_, lean_object* v_type_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_u_1230_, v_type_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec(v_a_1232_);
return v_res_1243_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2));
v___x_1251_ = l_Lean_stringToMessageData(v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object* v_u_1252_, lean_object* v_type_1253_, lean_object* v_semiringInst_x3f_1254_, lean_object* v_leInst_x3f_1255_, lean_object* v_ltInst_x3f_1256_, lean_object* v_preorderInst_x3f_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
if (lean_obj_tag(v_semiringInst_x3f_1254_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_1255_) == 1)
{
if (lean_obj_tag(v_ltInst_x3f_1256_) == 1)
{
if (lean_obj_tag(v_preorderInst_x3f_1257_) == 1)
{
lean_object* v_val_1268_; lean_object* v_val_1269_; lean_object* v_val_1270_; lean_object* v_val_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_isOrdType_1276_; lean_object* v___x_1277_; 
v_val_1268_ = lean_ctor_get(v_semiringInst_x3f_1254_, 0);
lean_inc(v_val_1268_);
lean_dec_ref(v_semiringInst_x3f_1254_);
v_val_1269_ = lean_ctor_get(v_leInst_x3f_1255_, 0);
lean_inc(v_val_1269_);
lean_dec_ref(v_leInst_x3f_1255_);
v_val_1270_ = lean_ctor_get(v_ltInst_x3f_1256_, 0);
lean_inc(v_val_1270_);
lean_dec_ref(v_ltInst_x3f_1256_);
v_val_1271_ = lean_ctor_get(v_preorderInst_x3f_1257_, 0);
lean_inc(v_val_1271_);
lean_dec_ref(v_preorderInst_x3f_1257_);
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_u_1252_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = l_Lean_mkConst(v___x_1272_, v___x_1274_);
v_isOrdType_1276_ = l_Lean_mkApp5(v___x_1275_, v_type_1253_, v_val_1268_, v_val_1269_, v_val_1270_, v_val_1271_);
lean_inc_ref(v_isOrdType_1276_);
v___x_1277_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_isOrdType_1276_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
if (lean_obj_tag(v_a_1278_) == 1)
{
lean_dec_ref(v_a_1278_);
lean_dec_ref(v_isOrdType_1276_);
return v___x_1277_;
}
else
{
lean_object* v___x_1279_; 
lean_dec_ref(v___x_1277_);
lean_dec(v_a_1278_);
v___x_1279_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1258_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; uint8_t v___x_1281_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = lean_unbox(v_a_1280_);
lean_dec(v_a_1280_);
if (v___x_1281_ == 0)
{
lean_dec_ref(v_isOrdType_1276_);
goto v___jp_1265_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3);
v___x_1283_ = l_Lean_indentExpr(v_isOrdType_1276_);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = l_Lean_Meta_Sym_reportIssue(v___x_1284_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_dec_ref(v___x_1285_);
goto v___jp_1265_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v_isOrdType_1276_);
v_a_1294_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1279_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1279_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
else
{
lean_dec_ref(v_isOrdType_1276_);
return v___x_1277_;
}
}
else
{
lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1309_; 
lean_dec_ref(v_leInst_x3f_1255_);
lean_dec_ref(v_semiringInst_x3f_1254_);
lean_dec(v_preorderInst_x3f_1257_);
lean_dec_ref(v_type_1253_);
lean_dec(v_u_1252_);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_ltInst_x3f_1256_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_ltInst_x3f_1256_, 0);
lean_dec(v_unused_1310_);
v___x_1303_ = v_ltInst_x3f_1256_;
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
else
{
lean_dec(v_ltInst_x3f_1256_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = lean_box(0);
if (v_isShared_1304_ == 0)
{
lean_ctor_set_tag(v___x_1303_, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1305_);
v___x_1307_ = v___x_1303_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
else
{
lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v_semiringInst_x3f_1254_);
lean_dec(v_preorderInst_x3f_1257_);
lean_dec(v_ltInst_x3f_1256_);
lean_dec_ref(v_type_1253_);
lean_dec(v_u_1252_);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_leInst_x3f_1255_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v_leInst_x3f_1255_, 0);
lean_dec(v_unused_1319_);
v___x_1312_ = v_leInst_x3f_1255_;
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v_leInst_x3f_1255_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = lean_box(0);
if (v_isShared_1313_ == 0)
{
lean_ctor_set_tag(v___x_1312_, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v_preorderInst_x3f_1257_);
lean_dec(v_ltInst_x3f_1256_);
lean_dec(v_leInst_x3f_1255_);
lean_dec_ref(v_type_1253_);
lean_dec(v_u_1252_);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_semiringInst_x3f_1254_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v_semiringInst_x3f_1254_, 0);
lean_dec(v_unused_1328_);
v___x_1321_ = v_semiringInst_x3f_1254_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_dec(v_semiringInst_x3f_1254_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = lean_box(0);
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec(v_preorderInst_x3f_1257_);
lean_dec(v_ltInst_x3f_1256_);
lean_dec(v_leInst_x3f_1255_);
lean_dec(v_semiringInst_x3f_1254_);
lean_dec_ref(v_type_1253_);
lean_dec(v_u_1252_);
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
v___jp_1265_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_1331_, lean_object* v_type_1332_, lean_object* v_semiringInst_x3f_1333_, lean_object* v_leInst_x3f_1334_, lean_object* v_ltInst_x3f_1335_, lean_object* v_preorderInst_x3f_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1331_, v_type_1332_, v_semiringInst_x3f_1333_, v_leInst_x3f_1334_, v_ltInst_x3f_1335_, v_preorderInst_x3f_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object* v_u_1345_, lean_object* v_type_1346_, lean_object* v_semiringInst_x3f_1347_, lean_object* v_leInst_x3f_1348_, lean_object* v_ltInst_x3f_1349_, lean_object* v_preorderInst_x3f_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1345_, v_type_1346_, v_semiringInst_x3f_1347_, v_leInst_x3f_1348_, v_ltInst_x3f_1349_, v_preorderInst_x3f_1350_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object** _args){
lean_object* v_u_1363_ = _args[0];
lean_object* v_type_1364_ = _args[1];
lean_object* v_semiringInst_x3f_1365_ = _args[2];
lean_object* v_leInst_x3f_1366_ = _args[3];
lean_object* v_ltInst_x3f_1367_ = _args[4];
lean_object* v_preorderInst_x3f_1368_ = _args[5];
lean_object* v_a_1369_ = _args[6];
lean_object* v_a_1370_ = _args[7];
lean_object* v_a_1371_ = _args[8];
lean_object* v_a_1372_ = _args[9];
lean_object* v_a_1373_ = _args[10];
lean_object* v_a_1374_ = _args[11];
lean_object* v_a_1375_ = _args[12];
lean_object* v_a_1376_ = _args[13];
lean_object* v_a_1377_ = _args[14];
lean_object* v_a_1378_ = _args[15];
lean_object* v_a_1379_ = _args[16];
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(v_u_1363_, v_type_1364_, v_semiringInst_x3f_1365_, v_leInst_x3f_1366_, v_ltInst_x3f_1367_, v_preorderInst_x3f_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec(v_a_1369_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object* v_u_1391_, lean_object* v_type_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v_natModuleType_1402_; lean_object* v___x_1403_; 
v___x_1398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_u_1391_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
lean_inc_ref(v___x_1400_);
v___x_1401_ = l_Lean_mkConst(v___x_1398_, v___x_1400_);
lean_inc_ref(v_type_1392_);
v_natModuleType_1402_ = l_Lean_Expr_app___override(v___x_1401_, v_type_1392_);
v___x_1403_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_natModuleType_1402_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1417_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1417_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1417_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
if (lean_obj_tag(v_a_1404_) == 1)
{
lean_object* v_val_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_del_object(v___x_1406_);
v_val_1408_ = lean_ctor_get(v_a_1404_, 0);
lean_inc(v_val_1408_);
lean_dec_ref(v_a_1404_);
v___x_1409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
v___x_1410_ = l_Lean_mkConst(v___x_1409_, v___x_1400_);
v___x_1411_ = l_Lean_mkAppB(v___x_1410_, v_type_1392_, v_val_1408_);
v___x_1412_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_1411_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
lean_dec(v_a_1404_);
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_type_1392_);
v___x_1413_ = lean_box(0);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1413_);
v___x_1415_ = v___x_1406_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
else
{
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_type_1392_);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object* v_u_1418_, lean_object* v_type_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1418_, v_type_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object* v_u_1426_, lean_object* v_type_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1426_, v_type_1427_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object* v_u_1440_, lean_object* v_type_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(v_u_1440_, v_type_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec(v_a_1442_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object* v_declName_1454_, lean_object* v_u_1455_, lean_object* v_type_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_u_1455_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = l_Lean_mkConst(v_declName_1454_, v___x_1463_);
v___x_1465_ = l_Lean_Expr_app___override(v___x_1464_, v_type_1456_);
v___x_1466_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_1465_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object* v_declName_1467_, lean_object* v_u_1468_, lean_object* v_type_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1467_, v_u_1468_, v_type_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object* v_declName_1476_, lean_object* v_u_1477_, lean_object* v_type_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1476_, v_u_1477_, v_type_1478_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object* v_declName_1491_, lean_object* v_u_1492_, lean_object* v_type_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(v_declName_1491_, v_u_1492_, v_type_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec(v_a_1494_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object* v_declName_1506_, lean_object* v_u_1507_, lean_object* v_type_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_u_1507_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = l_Lean_mkConst(v_declName_1506_, v___x_1521_);
v___x_1523_ = l_Lean_Expr_app___override(v___x_1522_, v_type_1508_);
v___x_1524_ = l_Lean_Meta_Grind_synthInstance(v___x_1523_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object* v_declName_1525_, lean_object* v_u_1526_, lean_object* v_type_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v_declName_1525_, v_u_1526_, v_type_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec(v_a_1528_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object* v_declName_1540_, lean_object* v_u_1541_, lean_object* v_type_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1554_ = lean_box(0);
lean_inc(v_u_1541_);
v___x_1555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_u_1541_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
lean_inc(v_u_1541_);
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_u_1541_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1557_, 0, v_u_1541_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_mkConst(v_declName_1540_, v___x_1557_);
lean_inc_ref_n(v_type_1542_, 2);
v___x_1559_ = l_Lean_mkApp3(v___x_1558_, v_type_1542_, v_type_1542_, v_type_1542_);
v___x_1560_ = l_Lean_Meta_Grind_synthInstance(v___x_1559_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object* v_declName_1561_, lean_object* v_u_1562_, lean_object* v_type_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v_declName_1561_, v_u_1562_, v_type_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec(v_a_1564_);
return v_res_1575_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = l_Lean_Level_ofNat(v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object* v_u_1581_, lean_object* v_type_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1));
v___x_1595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2);
v___x_1596_ = lean_box(0);
lean_inc(v_u_1581_);
v___x_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1597_, 0, v_u_1581_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_u_1581_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1595_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = l_Lean_mkConst(v___x_1594_, v___x_1599_);
v___x_1601_ = l_Lean_Int_mkType;
lean_inc_ref(v_type_1582_);
v___x_1602_ = l_Lean_mkApp3(v___x_1600_, v___x_1601_, v_type_1582_, v_type_1582_);
v___x_1603_ = l_Lean_Meta_Grind_synthInstance(v___x_1602_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object* v_u_1604_, lean_object* v_type_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(v_u_1604_, v_type_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec(v_a_1606_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object* v_u_1618_, lean_object* v_type_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1));
v___x_1632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2);
v___x_1633_ = lean_box(0);
lean_inc(v_u_1618_);
v___x_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_u_1618_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1635_, 0, v_u_1618_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1632_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_mkConst(v___x_1631_, v___x_1636_);
v___x_1638_ = l_Lean_Nat_mkType;
lean_inc_ref(v_type_1619_);
v___x_1639_ = l_Lean_mkApp3(v___x_1637_, v___x_1638_, v_type_1619_, v_type_1619_);
v___x_1640_ = l_Lean_Meta_Grind_synthInstance(v___x_1639_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object* v_u_1641_, lean_object* v_type_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_u_1641_, v_type_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec(v_a_1643_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object* v_leInst_x3f_1655_, lean_object* v_parentInst_x3f_1656_, lean_object* v_childInst_x3f_1657_, lean_object* v_toFieldName_1658_, lean_object* v_u_1659_, lean_object* v_type_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_1655_) == 1)
{
if (lean_obj_tag(v_parentInst_x3f_1656_) == 1)
{
if (lean_obj_tag(v_childInst_x3f_1657_) == 1)
{
lean_object* v_val_1671_; lean_object* v_val_1672_; lean_object* v_val_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v_toField_1677_; lean_object* v___x_1678_; 
v_val_1671_ = lean_ctor_get(v_leInst_x3f_1655_, 0);
lean_inc(v_val_1671_);
lean_dec_ref(v_leInst_x3f_1655_);
v_val_1672_ = lean_ctor_get(v_parentInst_x3f_1656_, 0);
lean_inc(v_val_1672_);
lean_dec_ref(v_parentInst_x3f_1656_);
v_val_1673_ = lean_ctor_get(v_childInst_x3f_1657_, 0);
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_u_1659_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = l_Lean_mkConst(v_toFieldName_1658_, v___x_1675_);
lean_inc(v_val_1673_);
v_toField_1677_ = l_Lean_mkApp3(v___x_1676_, v_type_1660_, v_val_1671_, v_val_1673_);
lean_inc_ref(v_toField_1677_);
lean_inc(v_val_1672_);
v___x_1678_ = l_Lean_Meta_isDefEqD(v_val_1672_, v_toField_1677_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1709_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1709_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1709_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
uint8_t v___x_1683_; 
v___x_1683_ = lean_unbox(v_a_1679_);
lean_dec(v_a_1679_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v_a_1685_; lean_object* v___x_1686_; 
lean_del_object(v___x_1681_);
lean_dec_ref(v_childInst_x3f_1657_);
v___x_1684_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_val_1672_, v_toField_1677_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1661_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; uint8_t v___x_1688_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = lean_unbox(v_a_1687_);
lean_dec(v_a_1687_);
if (v___x_1688_ == 0)
{
lean_dec(v_a_1685_);
goto v___jp_1668_;
}
else
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_Meta_Sym_reportIssue(v_a_1685_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_dec_ref(v___x_1689_);
goto v___jp_1668_;
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_a_1685_);
v_a_1698_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1686_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1686_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
else
{
lean_object* v___x_1707_; 
lean_dec_ref(v_toField_1677_);
lean_dec(v_val_1672_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v_childInst_x3f_1657_);
v___x_1707_ = v___x_1681_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_childInst_x3f_1657_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v_toField_1677_);
lean_dec(v_val_1672_);
lean_dec_ref(v_childInst_x3f_1657_);
v_a_1710_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1678_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1678_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
else
{
lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v_leInst_x3f_1655_);
lean_dec_ref(v_type_1660_);
lean_dec(v_u_1659_);
lean_dec(v_toFieldName_1658_);
lean_dec(v_childInst_x3f_1657_);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_parentInst_x3f_1656_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v_parentInst_x3f_1656_, 0);
lean_dec(v_unused_1726_);
v___x_1719_ = v_parentInst_x3f_1656_;
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
else
{
lean_dec(v_parentInst_x3f_1656_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = lean_box(0);
if (v_isShared_1720_ == 0)
{
lean_ctor_set_tag(v___x_1719_, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1721_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
lean_dec_ref(v_type_1660_);
lean_dec(v_u_1659_);
lean_dec(v_toFieldName_1658_);
lean_dec(v_childInst_x3f_1657_);
lean_dec(v_parentInst_x3f_1656_);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_leInst_x3f_1655_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v_leInst_x3f_1655_, 0);
lean_dec(v_unused_1735_);
v___x_1728_ = v_leInst_x3f_1655_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_dec(v_leInst_x3f_1655_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = lean_box(0);
if (v_isShared_1729_ == 0)
{
lean_ctor_set_tag(v___x_1728_, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1730_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec_ref(v_type_1660_);
lean_dec(v_u_1659_);
lean_dec(v_toFieldName_1658_);
lean_dec(v_childInst_x3f_1657_);
lean_dec(v_parentInst_x3f_1656_);
lean_dec(v_leInst_x3f_1655_);
v___x_1736_ = lean_box(0);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
v___jp_1668_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object* v_leInst_x3f_1738_, lean_object* v_parentInst_x3f_1739_, lean_object* v_childInst_x3f_1740_, lean_object* v_toFieldName_1741_, lean_object* v_u_1742_, lean_object* v_type_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1738_, v_parentInst_x3f_1739_, v_childInst_x3f_1740_, v_toFieldName_1741_, v_u_1742_, v_type_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object* v_leInst_x3f_1752_, lean_object* v_parentInst_x3f_1753_, lean_object* v_childInst_x3f_1754_, lean_object* v_toFieldName_1755_, lean_object* v_u_1756_, lean_object* v_type_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1752_, v_parentInst_x3f_1753_, v_childInst_x3f_1754_, v_toFieldName_1755_, v_u_1756_, v_type_1757_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object** _args){
lean_object* v_leInst_x3f_1770_ = _args[0];
lean_object* v_parentInst_x3f_1771_ = _args[1];
lean_object* v_childInst_x3f_1772_ = _args[2];
lean_object* v_toFieldName_1773_ = _args[3];
lean_object* v_u_1774_ = _args[4];
lean_object* v_type_1775_ = _args[5];
lean_object* v_a_1776_ = _args[6];
lean_object* v_a_1777_ = _args[7];
lean_object* v_a_1778_ = _args[8];
lean_object* v_a_1779_ = _args[9];
lean_object* v_a_1780_ = _args[10];
lean_object* v_a_1781_ = _args[11];
lean_object* v_a_1782_ = _args[12];
lean_object* v_a_1783_ = _args[13];
lean_object* v_a_1784_ = _args[14];
lean_object* v_a_1785_ = _args[15];
lean_object* v_a_1786_ = _args[16];
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(v_leInst_x3f_1770_, v_parentInst_x3f_1771_, v_childInst_x3f_1772_, v_toFieldName_1773_, v_u_1774_, v_type_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec(v_a_1776_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object* v_parentInst_1788_, lean_object* v_inst_1789_, lean_object* v_toFieldName_1790_, lean_object* v_u_1791_, lean_object* v_type_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v_toField_1801_; lean_object* v___x_1802_; 
v___x_1798_ = lean_box(0);
v___x_1799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1799_, 0, v_u_1791_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = l_Lean_mkConst(v_toFieldName_1790_, v___x_1799_);
v_toField_1801_ = l_Lean_mkAppB(v___x_1800_, v_type_1792_, v_inst_1789_);
v___x_1802_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1788_, v_toField_1801_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object* v_parentInst_1803_, lean_object* v_inst_1804_, lean_object* v_toFieldName_1805_, lean_object* v_u_1806_, lean_object* v_type_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1803_, v_inst_1804_, v_toFieldName_1805_, v_u_1806_, v_type_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object* v_parentInst_1814_, lean_object* v_inst_1815_, lean_object* v_toFieldName_1816_, lean_object* v_u_1817_, lean_object* v_type_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1814_, v_inst_1815_, v_toFieldName_1816_, v_u_1817_, v_type_1818_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object* v_parentInst_1831_, lean_object* v_inst_1832_, lean_object* v_toFieldName_1833_, lean_object* v_u_1834_, lean_object* v_type_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(v_parentInst_1831_, v_inst_1832_, v_toFieldName_1833_, v_u_1834_, v_type_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec(v_a_1836_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object* v_parentInst_1848_, lean_object* v_inst_1849_, lean_object* v_toFieldName_1850_, lean_object* v_toHeteroName_1851_, lean_object* v_u_1852_, lean_object* v_type_1853_, lean_object* v_extraType_x3f_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v_toField_1863_; 
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1861_, 0, v_u_1852_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
lean_inc_ref(v___x_1861_);
v___x_1862_ = l_Lean_mkConst(v_toFieldName_1850_, v___x_1861_);
lean_inc_ref(v_type_1853_);
v_toField_1863_ = l_Lean_mkAppB(v___x_1862_, v_type_1853_, v_inst_1849_);
if (lean_obj_tag(v_extraType_x3f_1854_) == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = l_Lean_mkConst(v_toHeteroName_1851_, v___x_1861_);
v___x_1865_ = l_Lean_mkAppB(v___x_1864_, v_type_1853_, v_toField_1863_);
v___x_1866_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1848_, v___x_1865_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
return v___x_1866_;
}
else
{
lean_object* v_val_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_val_1867_ = lean_ctor_get(v_extraType_x3f_1854_, 0);
lean_inc(v_val_1867_);
lean_dec_ref(v_extraType_x3f_1854_);
v___x_1868_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2);
v___x_1869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v___x_1861_);
v___x_1870_ = l_Lean_mkConst(v_toHeteroName_1851_, v___x_1869_);
v___x_1871_ = l_Lean_mkApp3(v___x_1870_, v_val_1867_, v_type_1853_, v_toField_1863_);
v___x_1872_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1848_, v___x_1871_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object* v_parentInst_1873_, lean_object* v_inst_1874_, lean_object* v_toFieldName_1875_, lean_object* v_toHeteroName_1876_, lean_object* v_u_1877_, lean_object* v_type_1878_, lean_object* v_extraType_x3f_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1873_, v_inst_1874_, v_toFieldName_1875_, v_toHeteroName_1876_, v_u_1877_, v_type_1878_, v_extraType_x3f_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object* v_parentInst_1886_, lean_object* v_inst_1887_, lean_object* v_toFieldName_1888_, lean_object* v_toHeteroName_1889_, lean_object* v_u_1890_, lean_object* v_type_1891_, lean_object* v_extraType_x3f_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1886_, v_inst_1887_, v_toFieldName_1888_, v_toHeteroName_1889_, v_u_1890_, v_type_1891_, v_extraType_x3f_1892_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object** _args){
lean_object* v_parentInst_1905_ = _args[0];
lean_object* v_inst_1906_ = _args[1];
lean_object* v_toFieldName_1907_ = _args[2];
lean_object* v_toHeteroName_1908_ = _args[3];
lean_object* v_u_1909_ = _args[4];
lean_object* v_type_1910_ = _args[5];
lean_object* v_extraType_x3f_1911_ = _args[6];
lean_object* v_a_1912_ = _args[7];
lean_object* v_a_1913_ = _args[8];
lean_object* v_a_1914_ = _args[9];
lean_object* v_a_1915_ = _args[10];
lean_object* v_a_1916_ = _args[11];
lean_object* v_a_1917_ = _args[12];
lean_object* v_a_1918_ = _args[13];
lean_object* v_a_1919_ = _args[14];
lean_object* v_a_1920_ = _args[15];
lean_object* v_a_1921_ = _args[16];
lean_object* v_a_1922_ = _args[17];
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(v_parentInst_1905_, v_inst_1906_, v_toFieldName_1907_, v_toHeteroName_1908_, v_u_1909_, v_type_1910_, v_extraType_x3f_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec(v_a_1912_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object* v_u_1928_, lean_object* v_type_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_smulType_1949_; lean_object* v___x_1950_; 
v___x_1941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1));
v___x_1942_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2);
v___x_1943_ = lean_box(0);
lean_inc(v_u_1928_);
v___x_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1944_, 0, v_u_1928_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1945_, 0, v_u_1928_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1942_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
lean_inc_ref(v___x_1946_);
v___x_1947_ = l_Lean_mkConst(v___x_1941_, v___x_1946_);
v___x_1948_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_1929_, 2);
v_smulType_1949_ = l_Lean_mkApp3(v___x_1947_, v___x_1948_, v_type_1929_, v_type_1929_);
v___x_1950_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_smulType_1949_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1987_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1987_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1987_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
if (lean_obj_tag(v_a_1951_) == 1)
{
lean_object* v_val_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1982_; 
lean_del_object(v___x_1953_);
v_val_1955_ = lean_ctor_get(v_a_1951_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_a_1951_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1957_ = v_a_1951_;
v_isShared_1958_ = v_isSharedCheck_1982_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_val_1955_);
lean_dec(v_a_1951_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1982_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
v___x_1960_ = l_Lean_mkConst(v___x_1959_, v___x_1946_);
lean_inc_ref(v_type_1929_);
v___x_1961_ = l_Lean_mkApp4(v___x_1960_, v___x_1948_, v_type_1929_, v_type_1929_, v_val_1955_);
v___x_1962_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_1961_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1973_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1973_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1973_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v_a_1963_);
v___x_1968_ = v___x_1957_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1970_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1968_);
v___x_1970_ = v___x_1965_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_del_object(v___x_1957_);
v_a_1974_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1962_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1962_);
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
else
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_dec(v_a_1951_);
lean_dec_ref(v___x_1946_);
lean_dec_ref(v_type_1929_);
v___x_1983_ = lean_box(0);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1983_);
v___x_1985_ = v___x_1953_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_dec_ref(v___x_1946_);
lean_dec_ref(v_type_1929_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object* v_u_1988_, lean_object* v_type_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(v_u_1988_, v_type_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec(v_a_1990_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object* v_u_2002_, lean_object* v_type_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v_smulType_2023_; lean_object* v___x_2024_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__1));
v___x_2016_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2);
v___x_2017_ = lean_box(0);
lean_inc(v_u_2002_);
v___x_2018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2018_, 0, v_u_2002_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
v___x_2019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2019_, 0, v_u_2002_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2016_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
lean_inc_ref(v___x_2020_);
v___x_2021_ = l_Lean_mkConst(v___x_2015_, v___x_2020_);
v___x_2022_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2003_, 2);
v_smulType_2023_ = l_Lean_mkApp3(v___x_2021_, v___x_2022_, v_type_2003_, v_type_2003_);
v___x_2024_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_smulType_2023_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2061_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2061_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2061_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
if (lean_obj_tag(v_a_2025_) == 1)
{
lean_object* v_val_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2056_; 
lean_del_object(v___x_2027_);
v_val_2029_ = lean_ctor_get(v_a_2025_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_a_2025_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2031_ = v_a_2025_;
v_isShared_2032_ = v_isSharedCheck_2056_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_val_2029_);
lean_dec(v_a_2025_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2056_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
v___x_2034_ = l_Lean_mkConst(v___x_2033_, v___x_2020_);
lean_inc_ref(v_type_2003_);
v___x_2035_ = l_Lean_mkApp4(v___x_2034_, v___x_2022_, v_type_2003_, v_type_2003_, v_val_2029_);
v___x_2036_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_2035_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2047_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v_a_2037_);
v___x_2042_ = v___x_2031_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2044_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2042_);
v___x_2044_ = v___x_2039_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_del_object(v___x_2031_);
v_a_2048_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2036_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2036_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
lean_dec(v_a_2025_);
lean_dec_ref(v___x_2020_);
lean_dec_ref(v_type_2003_);
v___x_2057_ = lean_box(0);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2057_);
v___x_2059_ = v___x_2027_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_dec_ref(v___x_2020_);
lean_dec_ref(v_type_2003_);
return v___x_2024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object* v_u_2062_, lean_object* v_type_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(v_u_2062_, v_type_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec(v_a_2064_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2076_, lean_object* v_x_2077_, lean_object* v_x_2078_, lean_object* v_x_2079_){
_start:
{
lean_object* v_ks_2080_; lean_object* v_vs_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2105_; 
v_ks_2080_ = lean_ctor_get(v_x_2076_, 0);
v_vs_2081_ = lean_ctor_get(v_x_2076_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_x_2076_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2083_ = v_x_2076_;
v_isShared_2084_ = v_isSharedCheck_2105_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_vs_2081_);
lean_inc(v_ks_2080_);
lean_dec(v_x_2076_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2105_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = lean_array_get_size(v_ks_2080_);
v___x_2086_ = lean_nat_dec_lt(v_x_2077_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
lean_dec(v_x_2077_);
v___x_2087_ = lean_array_push(v_ks_2080_, v_x_2078_);
v___x_2088_ = lean_array_push(v_vs_2081_, v_x_2079_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2088_);
lean_ctor_set(v___x_2083_, 0, v___x_2087_);
v___x_2090_ = v___x_2083_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
else
{
lean_object* v_k_x27_2092_; uint8_t v___x_2093_; 
v_k_x27_2092_ = lean_array_fget_borrowed(v_ks_2080_, v_x_2077_);
v___x_2093_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2078_, v_k_x27_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2095_; 
if (v_isShared_2084_ == 0)
{
v___x_2095_ = v___x_2083_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_ks_2080_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_vs_2081_);
v___x_2095_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_unsigned_to_nat(1u);
v___x_2097_ = lean_nat_add(v_x_2077_, v___x_2096_);
lean_dec(v_x_2077_);
v_x_2076_ = v___x_2095_;
v_x_2077_ = v___x_2097_;
goto _start;
}
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
v___x_2100_ = lean_array_fset(v_ks_2080_, v_x_2077_, v_x_2078_);
v___x_2101_ = lean_array_fset(v_vs_2081_, v_x_2077_, v_x_2079_);
lean_dec(v_x_2077_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2101_);
lean_ctor_set(v___x_2083_, 0, v___x_2100_);
v___x_2103_ = v___x_2083_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2106_, lean_object* v_k_2107_, lean_object* v_v_2108_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2106_, v___x_2109_, v_k_2107_, v_v_2108_);
return v___x_2110_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; 
v___x_2111_ = ((size_t)5ULL);
v___x_2112_ = ((size_t)1ULL);
v___x_2113_ = lean_usize_shift_left(v___x_2112_, v___x_2111_);
return v___x_2113_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2114_; size_t v___x_2115_; size_t v___x_2116_; 
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0);
v___x_2116_ = lean_usize_sub(v___x_2115_, v___x_2114_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(lean_object* v_x_2118_, size_t v_x_2119_, size_t v_x_2120_, lean_object* v_x_2121_, lean_object* v_x_2122_){
_start:
{
if (lean_obj_tag(v_x_2118_) == 0)
{
lean_object* v_es_2123_; size_t v___x_2124_; size_t v___x_2125_; size_t v___x_2126_; size_t v___x_2127_; lean_object* v_j_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v_es_2123_ = lean_ctor_get(v_x_2118_, 0);
v___x_2124_ = ((size_t)5ULL);
v___x_2125_ = ((size_t)1ULL);
v___x_2126_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1);
v___x_2127_ = lean_usize_land(v_x_2119_, v___x_2126_);
v_j_2128_ = lean_usize_to_nat(v___x_2127_);
v___x_2129_ = lean_array_get_size(v_es_2123_);
v___x_2130_ = lean_nat_dec_lt(v_j_2128_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_dec(v_j_2128_);
lean_dec(v_x_2122_);
lean_dec_ref(v_x_2121_);
return v_x_2118_;
}
else
{
lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2167_; 
lean_inc_ref(v_es_2123_);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_x_2118_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; 
v_unused_2168_ = lean_ctor_get(v_x_2118_, 0);
lean_dec(v_unused_2168_);
v___x_2132_ = v_x_2118_;
v_isShared_2133_ = v_isSharedCheck_2167_;
goto v_resetjp_2131_;
}
else
{
lean_dec(v_x_2118_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2167_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v_v_2134_; lean_object* v___x_2135_; lean_object* v_xs_x27_2136_; lean_object* v___y_2138_; 
v_v_2134_ = lean_array_fget(v_es_2123_, v_j_2128_);
v___x_2135_ = lean_box(0);
v_xs_x27_2136_ = lean_array_fset(v_es_2123_, v_j_2128_, v___x_2135_);
switch(lean_obj_tag(v_v_2134_))
{
case 0:
{
lean_object* v_key_2143_; lean_object* v_val_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2154_; 
v_key_2143_ = lean_ctor_get(v_v_2134_, 0);
v_val_2144_ = lean_ctor_get(v_v_2134_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_v_2134_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2146_ = v_v_2134_;
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_val_2144_);
lean_inc(v_key_2143_);
lean_dec(v_v_2134_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
uint8_t v___x_2148_; 
v___x_2148_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2121_, v_key_2143_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_del_object(v___x_2146_);
v___x_2149_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2143_, v_val_2144_, v_x_2121_, v_x_2122_);
v___x_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
v___y_2138_ = v___x_2150_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2152_; 
lean_dec(v_val_2144_);
lean_dec(v_key_2143_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v_x_2122_);
lean_ctor_set(v___x_2146_, 0, v_x_2121_);
v___x_2152_ = v___x_2146_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_x_2121_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_x_2122_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
v___y_2138_ = v___x_2152_;
goto v___jp_2137_;
}
}
}
}
case 1:
{
lean_object* v_node_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2165_; 
v_node_2155_ = lean_ctor_get(v_v_2134_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_v_2134_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2157_ = v_v_2134_;
v_isShared_2158_ = v_isSharedCheck_2165_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_node_2155_);
lean_dec(v_v_2134_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2165_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
size_t v___x_2159_; size_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2159_ = lean_usize_shift_right(v_x_2119_, v___x_2124_);
v___x_2160_ = lean_usize_add(v_x_2120_, v___x_2125_);
v___x_2161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(v_node_2155_, v___x_2159_, v___x_2160_, v_x_2121_, v_x_2122_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2161_);
v___x_2163_ = v___x_2157_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
v___y_2138_ = v___x_2163_;
goto v___jp_2137_;
}
}
}
default: 
{
lean_object* v___x_2166_; 
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v_x_2121_);
lean_ctor_set(v___x_2166_, 1, v_x_2122_);
v___y_2138_ = v___x_2166_;
goto v___jp_2137_;
}
}
v___jp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = lean_array_fset(v_xs_x27_2136_, v_j_2128_, v___y_2138_);
lean_dec(v_j_2128_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2139_);
v___x_2141_ = v___x_2132_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
else
{
lean_object* v_ks_2169_; lean_object* v_vs_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2190_; 
v_ks_2169_ = lean_ctor_get(v_x_2118_, 0);
v_vs_2170_ = lean_ctor_get(v_x_2118_, 1);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_x_2118_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2172_ = v_x_2118_;
v_isShared_2173_ = v_isSharedCheck_2190_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_vs_2170_);
lean_inc(v_ks_2169_);
lean_dec(v_x_2118_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2190_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_ks_2169_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_vs_2170_);
v___x_2175_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v_newNode_2176_; uint8_t v___y_2178_; size_t v___x_2184_; uint8_t v___x_2185_; 
v_newNode_2176_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(v___x_2175_, v_x_2121_, v_x_2122_);
v___x_2184_ = ((size_t)7ULL);
v___x_2185_ = lean_usize_dec_le(v___x_2184_, v_x_2120_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2186_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2176_);
v___x_2187_ = lean_unsigned_to_nat(4u);
v___x_2188_ = lean_nat_dec_lt(v___x_2186_, v___x_2187_);
lean_dec(v___x_2186_);
v___y_2178_ = v___x_2188_;
goto v___jp_2177_;
}
else
{
v___y_2178_ = v___x_2185_;
goto v___jp_2177_;
}
v___jp_2177_:
{
if (v___y_2178_ == 0)
{
lean_object* v_ks_2179_; lean_object* v_vs_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_ks_2179_ = lean_ctor_get(v_newNode_2176_, 0);
lean_inc_ref(v_ks_2179_);
v_vs_2180_ = lean_ctor_get(v_newNode_2176_, 1);
lean_inc_ref(v_vs_2180_);
lean_dec_ref(v_newNode_2176_);
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2);
v___x_2183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(v_x_2120_, v_ks_2179_, v_vs_2180_, v___x_2181_, v___x_2182_);
lean_dec_ref(v_vs_2180_);
lean_dec_ref(v_ks_2179_);
return v___x_2183_;
}
else
{
return v_newNode_2176_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(size_t v_depth_2191_, lean_object* v_keys_2192_, lean_object* v_vals_2193_, lean_object* v_i_2194_, lean_object* v_entries_2195_){
_start:
{
lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2196_ = lean_array_get_size(v_keys_2192_);
v___x_2197_ = lean_nat_dec_lt(v_i_2194_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_dec(v_i_2194_);
return v_entries_2195_;
}
else
{
lean_object* v_k_2198_; lean_object* v_v_2199_; uint64_t v___x_2200_; size_t v_h_2201_; size_t v___x_2202_; lean_object* v___x_2203_; size_t v___x_2204_; size_t v___x_2205_; size_t v___x_2206_; size_t v_h_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v_k_2198_ = lean_array_fget_borrowed(v_keys_2192_, v_i_2194_);
v_v_2199_ = lean_array_fget_borrowed(v_vals_2193_, v_i_2194_);
v___x_2200_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2198_);
v_h_2201_ = lean_uint64_to_usize(v___x_2200_);
v___x_2202_ = ((size_t)5ULL);
v___x_2203_ = lean_unsigned_to_nat(1u);
v___x_2204_ = ((size_t)1ULL);
v___x_2205_ = lean_usize_sub(v_depth_2191_, v___x_2204_);
v___x_2206_ = lean_usize_mul(v___x_2202_, v___x_2205_);
v_h_2207_ = lean_usize_shift_right(v_h_2201_, v___x_2206_);
v___x_2208_ = lean_nat_add(v_i_2194_, v___x_2203_);
lean_dec(v_i_2194_);
lean_inc(v_v_2199_);
lean_inc(v_k_2198_);
v___x_2209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(v_entries_2195_, v_h_2207_, v_depth_2191_, v_k_2198_, v_v_2199_);
v_i_2194_ = v___x_2208_;
v_entries_2195_ = v___x_2209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2211_, lean_object* v_keys_2212_, lean_object* v_vals_2213_, lean_object* v_i_2214_, lean_object* v_entries_2215_){
_start:
{
size_t v_depth_boxed_2216_; lean_object* v_res_2217_; 
v_depth_boxed_2216_ = lean_unbox_usize(v_depth_2211_);
lean_dec(v_depth_2211_);
v_res_2217_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2216_, v_keys_2212_, v_vals_2213_, v_i_2214_, v_entries_2215_);
lean_dec_ref(v_vals_2213_);
lean_dec_ref(v_keys_2212_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2218_, lean_object* v_x_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_){
_start:
{
size_t v_x_574731__boxed_2223_; size_t v_x_574732__boxed_2224_; lean_object* v_res_2225_; 
v_x_574731__boxed_2223_ = lean_unbox_usize(v_x_2219_);
lean_dec(v_x_2219_);
v_x_574732__boxed_2224_ = lean_unbox_usize(v_x_2220_);
lean_dec(v_x_2220_);
v_res_2225_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(v_x_2218_, v_x_574731__boxed_2223_, v_x_574732__boxed_2224_, v_x_2221_, v_x_2222_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_x_2226_, lean_object* v_x_2227_, lean_object* v_x_2228_){
_start:
{
uint64_t v___x_2229_; size_t v___x_2230_; size_t v___x_2231_; lean_object* v___x_2232_; 
v___x_2229_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2227_);
v___x_2230_ = lean_uint64_to_usize(v___x_2229_);
v___x_2231_ = ((size_t)1ULL);
v___x_2232_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(v_x_2226_, v___x_2230_, v___x_2231_, v_x_2227_, v_x_2228_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__0(lean_object* v_type_2233_, lean_object* v_s_2234_){
_start:
{
lean_object* v_structs_2235_; lean_object* v_typeIdOf_2236_; lean_object* v_exprToStructId_2237_; lean_object* v_exprToStructIdEntries_2238_; lean_object* v_forbiddenNatModules_2239_; lean_object* v_natStructs_2240_; lean_object* v_natTypeIdOf_2241_; lean_object* v_exprToNatStructId_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2251_; 
v_structs_2235_ = lean_ctor_get(v_s_2234_, 0);
v_typeIdOf_2236_ = lean_ctor_get(v_s_2234_, 1);
v_exprToStructId_2237_ = lean_ctor_get(v_s_2234_, 2);
v_exprToStructIdEntries_2238_ = lean_ctor_get(v_s_2234_, 3);
v_forbiddenNatModules_2239_ = lean_ctor_get(v_s_2234_, 4);
v_natStructs_2240_ = lean_ctor_get(v_s_2234_, 5);
v_natTypeIdOf_2241_ = lean_ctor_get(v_s_2234_, 6);
v_exprToNatStructId_2242_ = lean_ctor_get(v_s_2234_, 7);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_s_2234_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2244_ = v_s_2234_;
v_isShared_2245_ = v_isSharedCheck_2251_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_exprToNatStructId_2242_);
lean_inc(v_natTypeIdOf_2241_);
lean_inc(v_natStructs_2240_);
lean_inc(v_forbiddenNatModules_2239_);
lean_inc(v_exprToStructIdEntries_2238_);
lean_inc(v_exprToStructId_2237_);
lean_inc(v_typeIdOf_2236_);
lean_inc(v_structs_2235_);
lean_dec(v_s_2234_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2251_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2246_ = lean_box(0);
v___x_2247_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(v_forbiddenNatModules_2239_, v_type_2233_, v___x_2246_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v___x_2247_);
v___x_2249_ = v___x_2244_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_structs_2235_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_typeIdOf_2236_);
lean_ctor_set(v_reuseFailAlloc_2250_, 2, v_exprToStructId_2237_);
lean_ctor_set(v_reuseFailAlloc_2250_, 3, v_exprToStructIdEntries_2238_);
lean_ctor_set(v_reuseFailAlloc_2250_, 4, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2250_, 5, v_natStructs_2240_);
lean_ctor_set(v_reuseFailAlloc_2250_, 6, v_natTypeIdOf_2241_);
lean_ctor_set(v_reuseFailAlloc_2250_, 7, v_exprToNatStructId_2242_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(lean_object* v_a_2252_, lean_object* v_00___2253_){
_start:
{
if (lean_obj_tag(v_a_2252_) == 0)
{
uint8_t v___x_2254_; 
v___x_2254_ = 0;
return v___x_2254_;
}
else
{
uint8_t v___x_2255_; 
v___x_2255_ = 1;
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1___boxed(lean_object* v_a_2256_, lean_object* v_00___2257_){
_start:
{
uint8_t v_res_2258_; lean_object* v_r_2259_; 
v_res_2258_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(v_a_2256_, v_00___2257_);
lean_dec(v_a_2256_);
v_r_2259_ = lean_box(v_res_2258_);
return v_r_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__2(lean_object* v___x_2260_, lean_object* v_s_2261_){
_start:
{
lean_object* v_structs_2262_; lean_object* v_typeIdOf_2263_; lean_object* v_exprToStructId_2264_; lean_object* v_exprToStructIdEntries_2265_; lean_object* v_forbiddenNatModules_2266_; lean_object* v_natStructs_2267_; lean_object* v_natTypeIdOf_2268_; lean_object* v_exprToNatStructId_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2277_; 
v_structs_2262_ = lean_ctor_get(v_s_2261_, 0);
v_typeIdOf_2263_ = lean_ctor_get(v_s_2261_, 1);
v_exprToStructId_2264_ = lean_ctor_get(v_s_2261_, 2);
v_exprToStructIdEntries_2265_ = lean_ctor_get(v_s_2261_, 3);
v_forbiddenNatModules_2266_ = lean_ctor_get(v_s_2261_, 4);
v_natStructs_2267_ = lean_ctor_get(v_s_2261_, 5);
v_natTypeIdOf_2268_ = lean_ctor_get(v_s_2261_, 6);
v_exprToNatStructId_2269_ = lean_ctor_get(v_s_2261_, 7);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_s_2261_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2271_ = v_s_2261_;
v_isShared_2272_ = v_isSharedCheck_2277_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_exprToNatStructId_2269_);
lean_inc(v_natTypeIdOf_2268_);
lean_inc(v_natStructs_2267_);
lean_inc(v_forbiddenNatModules_2266_);
lean_inc(v_exprToStructIdEntries_2265_);
lean_inc(v_exprToStructId_2264_);
lean_inc(v_typeIdOf_2263_);
lean_inc(v_structs_2262_);
lean_dec(v_s_2261_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2277_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2273_ = lean_array_push(v_structs_2262_, v___x_2260_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2273_);
v___x_2275_ = v___x_2271_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_typeIdOf_2263_);
lean_ctor_set(v_reuseFailAlloc_2276_, 2, v_exprToStructId_2264_);
lean_ctor_set(v_reuseFailAlloc_2276_, 3, v_exprToStructIdEntries_2265_);
lean_ctor_set(v_reuseFailAlloc_2276_, 4, v_forbiddenNatModules_2266_);
lean_ctor_set(v_reuseFailAlloc_2276_, 5, v_natStructs_2267_);
lean_ctor_set(v_reuseFailAlloc_2276_, 6, v_natTypeIdOf_2268_);
lean_ctor_set(v_reuseFailAlloc_2276_, 7, v_exprToNatStructId_2269_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = lean_unsigned_to_nat(32u);
v___x_2285_ = lean_mk_empty_array_with_capacity(v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2287_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_unsigned_to_nat(0u);
v___x_2312_ = l_Lean_mkRawNatLit(v___x_2311_);
return v___x_2312_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = l_Lean_Int_mkType;
v___x_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = l_Lean_Nat_mkType;
v___x_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object* v_type_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v___y_2411_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2426_; lean_object* v___y_2427_; uint8_t v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2451_; lean_object* v___y_2452_; uint8_t v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___x_2476_; 
lean_inc_ref(v_type_2398_);
v___x_2476_ = l_Lean_Meta_getDecLevel_x3f(v_type_2398_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_3394_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_3394_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_3394_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
if (lean_obj_tag(v_a_2477_) == 1)
{
lean_object* v_val_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_3389_; 
lean_del_object(v___x_2479_);
v_val_2481_ = lean_ctor_get(v_a_2477_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_a_2477_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_2483_ = v_a_2477_;
v_isShared_2484_ = v_isSharedCheck_3389_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_val_2481_);
lean_dec(v_a_2477_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_3389_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2485_; 
lean_inc_ref(v_type_2398_);
v___x_2485_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_3388_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_3388_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_3388_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2491_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2490_, v_val_2481_, v_type_2398_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref(v___x_2491_);
v___x_2493_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3));
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2494_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2493_, v_val_2481_, v_type_2398_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2496_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref(v___x_2494_);
lean_inc(v_a_2492_);
lean_inc(v_a_2495_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2496_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_val_2481_, v_type_2398_, v_a_2495_, v_a_2492_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; uint8_t v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v_homomulFn_x3f_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; uint8_t v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v_ltFn_x3f_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; uint8_t v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v_leFn_x3f_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; uint8_t v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v_charInst_x3f_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___x_3009_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref(v___x_2496_);
lean_inc(v_a_2492_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_3009_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_2481_, v_type_2398_, v_a_2492_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref(v___x_3009_);
lean_inc(v_a_2492_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_3011_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_val_2481_, v_type_2398_, v_a_2492_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref(v___x_3011_);
lean_inc(v_a_2492_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_3013_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_val_2481_, v_type_2398_, v_a_2492_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; uint8_t v___y_3036_; lean_object* v___x_3123_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref(v___x_3013_);
v___x_3123_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2401_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; uint8_t v_ring_3125_; lean_object* v___f_3126_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; uint8_t v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; uint8_t v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3204_; lean_object* v___y_3205_; uint8_t v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; uint8_t v___y_3225_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref(v___x_3123_);
v_ring_3125_ = lean_ctor_get_uint8(v_a_3124_, sizeof(void*)*11 + 21);
lean_dec(v_a_3124_);
lean_inc_ref(v_type_2398_);
v___f_3126_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_3126_, 0, v_type_2398_);
if (v_ring_3125_ == 0)
{
v___y_3225_ = v_ring_3125_;
goto v___jp_3224_;
}
else
{
lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3310_ = lean_box(0);
v___x_3311_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(v_a_2486_, v___x_3310_);
if (v___x_3311_ == 0)
{
v___y_3225_ = v___x_3311_;
goto v___jp_3224_;
}
else
{
if (lean_obj_tag(v_a_3010_) == 0)
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec(v_a_3014_);
lean_dec(v_a_3012_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v___x_3312_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3313_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3312_, v___f_3126_, v_a_2399_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3321_; 
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3321_ == 0)
{
lean_object* v_unused_3322_; 
v_unused_3322_ = lean_ctor_get(v___x_3313_, 0);
lean_dec(v_unused_3322_);
v___x_3315_ = v___x_3313_;
v_isShared_3316_ = v_isSharedCheck_3321_;
goto v_resetjp_3314_;
}
else
{
lean_dec(v___x_3313_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3321_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3317_ = lean_box(0);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 0, v___x_3317_);
v___x_3319_ = v___x_3315_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
v_a_3323_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3313_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3313_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
else
{
uint8_t v___x_3331_; 
v___x_3331_ = 0;
v___y_3225_ = v___x_3331_;
goto v___jp_3224_;
}
}
}
v___jp_3127_:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3134_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; uint8_t v_ring_3151_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc(v_a_3150_);
lean_dec_ref(v___x_3149_);
v_ring_3151_ = lean_ctor_get_uint8(v_a_3150_, sizeof(void*)*11 + 21);
lean_dec(v_a_3150_);
if (v_ring_3151_ == 0)
{
lean_dec_ref(v___f_3126_);
v___y_3016_ = v___y_3128_;
v___y_3017_ = v___y_3129_;
v___y_3018_ = v___y_3130_;
v___y_3019_ = v___y_3131_;
v___y_3020_ = v___y_3133_;
v___y_3021_ = v___y_3134_;
v___y_3022_ = v___y_3135_;
v___y_3023_ = v___y_3136_;
v___y_3024_ = v___y_3137_;
v___y_3025_ = v___y_3138_;
v___y_3026_ = v___y_3139_;
v___y_3027_ = v___y_3141_;
v___y_3028_ = v___y_3140_;
v___y_3029_ = v___y_3142_;
v___y_3030_ = v___y_3143_;
v___y_3031_ = v___y_3144_;
v___y_3032_ = v___y_3145_;
v___y_3033_ = v___y_3148_;
v___y_3034_ = v___y_3146_;
v___y_3035_ = v___y_3147_;
v___y_3036_ = v_ring_3151_;
goto v___jp_3015_;
}
else
{
lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3152_ = lean_box(0);
v___x_3153_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(v_a_2486_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_dec_ref(v___f_3126_);
v___y_3016_ = v___y_3128_;
v___y_3017_ = v___y_3129_;
v___y_3018_ = v___y_3130_;
v___y_3019_ = v___y_3131_;
v___y_3020_ = v___y_3133_;
v___y_3021_ = v___y_3134_;
v___y_3022_ = v___y_3135_;
v___y_3023_ = v___y_3136_;
v___y_3024_ = v___y_3137_;
v___y_3025_ = v___y_3138_;
v___y_3026_ = v___y_3139_;
v___y_3027_ = v___y_3141_;
v___y_3028_ = v___y_3140_;
v___y_3029_ = v___y_3142_;
v___y_3030_ = v___y_3143_;
v___y_3031_ = v___y_3144_;
v___y_3032_ = v___y_3145_;
v___y_3033_ = v___y_3148_;
v___y_3034_ = v___y_3146_;
v___y_3035_ = v___y_3147_;
v___y_3036_ = v___x_3153_;
goto v___jp_3015_;
}
else
{
if (lean_obj_tag(v___y_3148_) == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3135_);
lean_dec(v___y_3133_);
lean_dec(v___y_3130_);
lean_dec(v___y_3128_);
lean_dec(v_a_3014_);
lean_dec(v_a_3012_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v___x_3154_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3155_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3154_, v___f_3126_, v___y_3137_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3163_; 
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; 
v_unused_3164_ = lean_ctor_get(v___x_3155_, 0);
lean_dec(v_unused_3164_);
v___x_3157_ = v___x_3155_;
v_isShared_3158_ = v_isSharedCheck_3163_;
goto v_resetjp_3156_;
}
else
{
lean_dec(v___x_3155_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3163_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3159_ = lean_box(0);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3159_);
v___x_3161_ = v___x_3157_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
v_a_3165_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3155_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3155_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
else
{
lean_dec_ref(v___f_3126_);
v___y_3016_ = v___y_3128_;
v___y_3017_ = v___y_3129_;
v___y_3018_ = v___y_3130_;
v___y_3019_ = v___y_3131_;
v___y_3020_ = v___y_3133_;
v___y_3021_ = v___y_3134_;
v___y_3022_ = v___y_3135_;
v___y_3023_ = v___y_3136_;
v___y_3024_ = v___y_3137_;
v___y_3025_ = v___y_3138_;
v___y_3026_ = v___y_3139_;
v___y_3027_ = v___y_3141_;
v___y_3028_ = v___y_3140_;
v___y_3029_ = v___y_3142_;
v___y_3030_ = v___y_3143_;
v___y_3031_ = v___y_3144_;
v___y_3032_ = v___y_3145_;
v___y_3033_ = v___y_3148_;
v___y_3034_ = v___y_3146_;
v___y_3035_ = v___y_3147_;
v___y_3036_ = v___y_3132_;
goto v___jp_3015_;
}
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_dec(v___y_3148_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3135_);
lean_dec(v___y_3133_);
lean_dec(v___y_3130_);
lean_dec(v___y_3128_);
lean_dec_ref(v___f_3126_);
lean_dec(v_a_3014_);
lean_dec(v_a_3012_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3173_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3149_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3149_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
v___jp_3181_:
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_box(0);
v___y_3128_ = v___y_3182_;
v___y_3129_ = v___y_3183_;
v___y_3130_ = v___y_3184_;
v___y_3131_ = v___y_3185_;
v___y_3132_ = v___y_3186_;
v___y_3133_ = v___y_3187_;
v___y_3134_ = v___y_3188_;
v___y_3135_ = v___y_3189_;
v___y_3136_ = v___y_3190_;
v___y_3137_ = v___y_3191_;
v___y_3138_ = v___y_3192_;
v___y_3139_ = v___y_3193_;
v___y_3140_ = v___y_3195_;
v___y_3141_ = v___y_3194_;
v___y_3142_ = v___y_3196_;
v___y_3143_ = v___y_3197_;
v___y_3144_ = v___y_3198_;
v___y_3145_ = v___y_3199_;
v___y_3146_ = v___y_3200_;
v___y_3147_ = v___y_3201_;
v___y_3148_ = v___x_3202_;
goto v___jp_3127_;
}
v___jp_3203_:
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_box(0);
v___y_3182_ = v___x_3223_;
v___y_3183_ = v___y_3222_;
v___y_3184_ = v___y_3205_;
v___y_3185_ = v___y_3220_;
v___y_3186_ = v___y_3206_;
v___y_3187_ = v___y_3208_;
v___y_3188_ = v___y_3215_;
v___y_3189_ = v___y_3212_;
v___y_3190_ = v___y_3219_;
v___y_3191_ = v___y_3213_;
v___y_3192_ = v___y_3214_;
v___y_3193_ = v___y_3204_;
v___y_3194_ = v___y_3216_;
v___y_3195_ = v___y_3217_;
v___y_3196_ = v___y_3218_;
v___y_3197_ = v___y_3207_;
v___y_3198_ = v___y_3209_;
v___y_3199_ = v___y_3210_;
v___y_3200_ = v___y_3211_;
v___y_3201_ = v___y_3221_;
goto v___jp_3181_;
}
v___jp_3224_:
{
lean_object* v___x_3226_; 
lean_inc(v_a_2486_);
v___x_3226_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_a_2486_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3228_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref(v___x_3226_);
lean_inc(v_a_3227_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_3228_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_val_2481_, v_type_2398_, v_a_3227_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref(v___x_3228_);
lean_inc(v_a_3229_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_3230_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_val_2481_, v_type_2398_, v_a_3229_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3285_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3233_ = v___x_3230_;
v_isShared_3234_ = v_isSharedCheck_3285_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3285_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
if (lean_obj_tag(v_a_3231_) == 1)
{
lean_object* v_val_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_del_object(v___x_3233_);
v_val_3235_ = lean_ctor_get(v_a_3231_, 0);
lean_inc(v_val_3235_);
lean_dec_ref(v_a_3231_);
v___x_3236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62));
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_3237_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v___x_3236_, v_val_2481_, v_type_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref(v___x_3237_);
v___x_3239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64));
v___x_3240_ = lean_box(0);
lean_inc(v_val_2481_);
v___x_3241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3241_, 0, v_val_2481_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
lean_inc_ref(v___x_3241_);
lean_inc(v_val_2481_);
v___x_3242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3242_, 0, v_val_2481_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
lean_inc_ref(v___x_3242_);
lean_inc(v_val_2481_);
v___x_3243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3243_, 0, v_val_2481_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
lean_inc_ref(v___x_3243_);
v___x_3244_ = l_Lean_mkConst(v___x_3239_, v___x_3243_);
lean_inc(v_a_3238_);
lean_inc_ref_n(v_type_2398_, 3);
v___x_3245_ = l_Lean_mkApp4(v___x_3244_, v_type_2398_, v_type_2398_, v_type_2398_, v_a_3238_);
v___x_3246_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_3245_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_3246_) == 0)
{
if (lean_obj_tag(v_a_2492_) == 1)
{
if (lean_obj_tag(v_a_3010_) == 1)
{
lean_object* v_a_3247_; lean_object* v_val_3248_; lean_object* v_val_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref(v___x_3246_);
v_val_3248_ = lean_ctor_get(v_a_2492_, 0);
v_val_3249_ = lean_ctor_get(v_a_3010_, 0);
v___x_3250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66));
lean_inc_ref(v___x_3241_);
v___x_3251_ = l_Lean_mkConst(v___x_3250_, v___x_3241_);
lean_inc(v_val_3249_);
lean_inc(v_val_3248_);
lean_inc(v_a_3238_);
lean_inc_ref(v_type_2398_);
v___x_3252_ = l_Lean_mkApp4(v___x_3251_, v_type_2398_, v_a_3238_, v_val_3248_, v_val_3249_);
v___x_3253_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_3252_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref(v___x_3253_);
if (lean_obj_tag(v_a_3254_) == 0)
{
lean_dec_ref(v_a_3010_);
v___y_3182_ = v_a_3254_;
v___y_3183_ = v_a_2408_;
v___y_3184_ = v___x_3241_;
v___y_3185_ = v_a_2406_;
v___y_3186_ = v___y_3225_;
v___y_3187_ = v_a_3229_;
v___y_3188_ = v_a_2401_;
v___y_3189_ = v___x_3243_;
v___y_3190_ = v_a_2405_;
v___y_3191_ = v_a_2399_;
v___y_3192_ = v_a_2400_;
v___y_3193_ = v_val_3235_;
v___y_3194_ = v_a_2402_;
v___y_3195_ = v_a_2403_;
v___y_3196_ = v_a_2404_;
v___y_3197_ = v_a_3227_;
v___y_3198_ = v_a_3247_;
v___y_3199_ = v_a_3238_;
v___y_3200_ = v___x_3242_;
v___y_3201_ = v_a_2407_;
goto v___jp_3181_;
}
else
{
if (v___y_3225_ == 0)
{
v___y_3128_ = v_a_3254_;
v___y_3129_ = v_a_2408_;
v___y_3130_ = v___x_3241_;
v___y_3131_ = v_a_2406_;
v___y_3132_ = v___y_3225_;
v___y_3133_ = v_a_3229_;
v___y_3134_ = v_a_2401_;
v___y_3135_ = v___x_3243_;
v___y_3136_ = v_a_2405_;
v___y_3137_ = v_a_2399_;
v___y_3138_ = v_a_2400_;
v___y_3139_ = v_val_3235_;
v___y_3140_ = v_a_2403_;
v___y_3141_ = v_a_2402_;
v___y_3142_ = v_a_2404_;
v___y_3143_ = v_a_3227_;
v___y_3144_ = v_a_3247_;
v___y_3145_ = v_a_3238_;
v___y_3146_ = v___x_3242_;
v___y_3147_ = v_a_2407_;
v___y_3148_ = v_a_3010_;
goto v___jp_3127_;
}
else
{
lean_dec_ref(v_a_3010_);
v___y_3182_ = v_a_3254_;
v___y_3183_ = v_a_2408_;
v___y_3184_ = v___x_3241_;
v___y_3185_ = v_a_2406_;
v___y_3186_ = v___y_3225_;
v___y_3187_ = v_a_3229_;
v___y_3188_ = v_a_2401_;
v___y_3189_ = v___x_3243_;
v___y_3190_ = v_a_2405_;
v___y_3191_ = v_a_2399_;
v___y_3192_ = v_a_2400_;
v___y_3193_ = v_val_3235_;
v___y_3194_ = v_a_2402_;
v___y_3195_ = v_a_2403_;
v___y_3196_ = v_a_2404_;
v___y_3197_ = v_a_3227_;
v___y_3198_ = v_a_3247_;
v___y_3199_ = v_a_3238_;
v___y_3200_ = v___x_3242_;
v___y_3201_ = v_a_2407_;
goto v___jp_3181_;
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_2492_);
lean_dec_ref(v___x_3243_);
lean_dec_ref(v___x_3242_);
lean_dec_ref(v___x_3241_);
lean_dec(v_a_3238_);
lean_dec(v_val_3235_);
lean_dec(v_a_3229_);
lean_dec(v_a_3227_);
lean_dec_ref(v___f_3126_);
lean_dec(v_a_3014_);
lean_dec(v_a_3012_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3255_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3253_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3253_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
else
{
lean_object* v_a_3263_; 
lean_dec(v_a_3010_);
v_a_3263_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3263_);
lean_dec_ref(v___x_3246_);
v___y_3204_ = v_val_3235_;
v___y_3205_ = v___x_3241_;
v___y_3206_ = v___y_3225_;
v___y_3207_ = v_a_3227_;
v___y_3208_ = v_a_3229_;
v___y_3209_ = v_a_3263_;
v___y_3210_ = v_a_3238_;
v___y_3211_ = v___x_3242_;
v___y_3212_ = v___x_3243_;
v___y_3213_ = v_a_2399_;
v___y_3214_ = v_a_2400_;
v___y_3215_ = v_a_2401_;
v___y_3216_ = v_a_2402_;
v___y_3217_ = v_a_2403_;
v___y_3218_ = v_a_2404_;
v___y_3219_ = v_a_2405_;
v___y_3220_ = v_a_2406_;
v___y_3221_ = v_a_2407_;
v___y_3222_ = v_a_2408_;
goto v___jp_3203_;
}
}
else
{
lean_object* v_a_3264_; 
lean_dec(v_a_3010_);
v_a_3264_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3264_);
lean_dec_ref(v___x_3246_);
v___y_3204_ = v_val_3235_;
v___y_3205_ = v___x_3241_;
v___y_3206_ = v___y_3225_;
v___y_3207_ = v_a_3227_;
v___y_3208_ = v_a_3229_;
v___y_3209_ = v_a_3264_;
v___y_3210_ = v_a_3238_;
v___y_3211_ = v___x_3242_;
v___y_3212_ = v___x_3243_;
v___y_3213_ = v_a_2399_;
v___y_3214_ = v_a_2400_;
v___y_3215_ = v_a_2401_;
v___y_3216_ = v_a_2402_;
v___y_3217_ = v_a_2403_;
v___y_3218_ = v_a_2404_;
v___y_3219_ = v_a_2405_;
v___y_3220_ = v_a_2406_;
v___y_3221_ = v_a_2407_;
v___y_3222_ = v_a_2408_;
goto v___jp_3203_;
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec_ref(v___x_3243_);
lean_dec_ref(v___x_3242_);
lean_dec_ref(v___x_3241_);
lean_dec(v_a_3238_);
lean_dec(v_val_3235_);
lean_dec(v_a_3229_);
lean_dec(v_a_3227_);
lean_dec_ref(v___f_3126_);
lean_dec(v_a_3014_);
lean_dec(v_a_3012_);
lean_dec(v_a_3010_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3265_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3246_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3246_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec(v_val_3235_);
lean_dec(v_a_3229_);
lean_dec(v_a_3227_);
lean_dec_ref(v___f_3126_);
lean_dec(v_a_3014_);
lean_dec(v_a_3012_);
lean_dec(v_a_3010_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3273_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3237_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3237_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_dec(v_a_3231_);
lean_dec(v_a_3229_);
lean_dec(v_a_3227_);
lean_dec_ref(v___f_3126_);
lean_dec(v_a_3014_);
lean_dec(v_a_3012_);
lean_dec(v_a_3010_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v___x_3281_ = lean_box(0);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v___x_3281_);
v___x_3283_ = v___x_3233_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v_a_3229_);
lean_dec(v_a_3227_);
lean_dec_ref(v___f_3126_);
lean_dec(v_a_3014_);
lean_dec(v_a_3012_);
lean_dec(v_a_3010_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3286_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3230_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3230_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec(v_a_3227_);
lean_dec_ref(v___f_3126_);
lean_dec(v_a_3014_);
lean_dec(v_a_3012_);
lean_dec(v_a_3010_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3294_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3228_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3228_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v___f_3126_);
lean_dec(v_a_3014_);
lean_dec(v_a_3012_);
lean_dec(v_a_3010_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3302_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3226_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3226_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_dec(v_a_3014_);
lean_dec(v_a_3012_);
lean_dec(v_a_3010_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3332_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3123_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3123_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
v___jp_3015_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50));
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
lean_inc(v___y_3033_);
lean_inc(v_a_2492_);
v___x_3038_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2492_, v___y_3033_, v_a_3012_, v___x_3037_, v_val_2481_, v_type_2398_, v___y_3028_, v___y_3029_, v___y_3023_, v___y_3019_, v___y_3035_, v___y_3017_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref(v___x_3038_);
v___x_3040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53));
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
lean_inc(v_a_2492_);
v___x_3041_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2492_, v_a_3039_, v_a_3014_, v___x_3040_, v_val_2481_, v_type_2398_, v___y_3028_, v___y_3029_, v___y_3023_, v___y_3019_, v___y_3035_, v___y_3017_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref(v___x_3041_);
v___x_3043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_3044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_3045_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_3046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55));
lean_inc(v___y_3018_);
v___x_3047_ = l_Lean_mkConst(v___x_3046_, v___y_3018_);
lean_inc_ref(v___y_3026_);
lean_inc_ref(v_type_2398_);
v___x_3048_ = l_Lean_mkAppB(v___x_3047_, v_type_2398_, v___y_3026_);
v___x_3049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56));
v___x_3050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58));
lean_inc(v___y_3018_);
v___x_3051_ = l_Lean_mkConst(v___x_3050_, v___y_3018_);
lean_inc_ref(v___x_3048_);
lean_inc_ref(v_type_2398_);
v___x_3052_ = l_Lean_mkAppB(v___x_3051_, v_type_2398_, v___x_3048_);
lean_inc(v___y_3020_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_3053_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_val_2481_, v_type_2398_, v___y_3020_, v___y_3023_, v___y_3019_, v___y_3035_, v___y_3017_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref(v___x_3053_);
v___x_3055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60));
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_3056_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3055_, v_val_2481_, v_type_2398_, v___y_3023_, v___y_3019_, v___y_3035_, v___y_3017_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3058_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref(v___x_3056_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_3058_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_val_2481_, v_type_2398_, v___y_3024_, v___y_3025_, v___y_3021_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3023_, v___y_3019_, v___y_3035_, v___y_3017_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
lean_inc(v___y_3033_);
lean_inc(v_a_2495_);
lean_inc(v_a_2492_);
lean_inc(v_a_3054_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_3060_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_val_2481_, v_type_2398_, v_a_3054_, v_a_2492_, v_a_2495_, v___y_3033_, v___y_3028_, v___y_3029_, v___y_3023_, v___y_3019_, v___y_3035_, v___y_3017_);
if (lean_obj_tag(v___x_3060_) == 0)
{
if (lean_obj_tag(v_a_3054_) == 1)
{
lean_object* v_a_3061_; lean_object* v_val_3062_; lean_object* v___x_3063_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref(v___x_3060_);
v_val_3062_ = lean_ctor_get(v_a_3054_, 0);
lean_inc(v_val_3062_);
lean_dec_ref(v_a_3054_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_3063_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_val_2481_, v_type_2398_, v_val_3062_, v___y_3024_, v___y_3025_, v___y_3021_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3023_, v___y_3019_, v___y_3035_, v___y_3017_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref(v___x_3063_);
v___y_2707_ = v___x_3052_;
v___y_2708_ = v_a_3042_;
v___y_2709_ = v_a_3061_;
v___y_2710_ = v___y_3018_;
v___y_2711_ = v___y_3016_;
v___y_2712_ = v___x_3044_;
v___y_2713_ = v___y_3020_;
v___y_2714_ = v___x_3049_;
v___y_2715_ = v___y_3036_;
v___y_2716_ = v___y_3022_;
v___y_2717_ = v___x_3043_;
v___y_2718_ = v___x_3048_;
v___y_2719_ = v___y_3026_;
v___y_2720_ = v___y_3030_;
v___y_2721_ = v___y_3031_;
v___y_2722_ = v___y_3032_;
v___y_2723_ = v___y_3033_;
v___y_2724_ = v___x_3045_;
v___y_2725_ = v___y_3034_;
v___y_2726_ = v_a_3059_;
v___y_2727_ = v_a_3057_;
v_charInst_x3f_2728_ = v_a_3064_;
v___y_2729_ = v___y_3024_;
v___y_2730_ = v___y_3025_;
v___y_2731_ = v___y_3021_;
v___y_2732_ = v___y_3027_;
v___y_2733_ = v___y_3028_;
v___y_2734_ = v___y_3029_;
v___y_2735_ = v___y_3023_;
v___y_2736_ = v___y_3019_;
v___y_2737_ = v___y_3035_;
v___y_2738_ = v___y_3017_;
goto v___jp_2706_;
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec(v_a_3061_);
lean_dec(v_a_3059_);
lean_dec(v_a_3057_);
lean_dec_ref(v___x_3052_);
lean_dec_ref(v___x_3048_);
lean_dec(v_a_3042_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3022_);
lean_dec(v___y_3020_);
lean_dec(v___y_3018_);
lean_dec(v___y_3016_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3065_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3063_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3063_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3074_; 
lean_dec(v_a_3054_);
v_a_3073_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3073_);
lean_dec_ref(v___x_3060_);
v___x_3074_ = lean_box(0);
v___y_2707_ = v___x_3052_;
v___y_2708_ = v_a_3042_;
v___y_2709_ = v_a_3073_;
v___y_2710_ = v___y_3018_;
v___y_2711_ = v___y_3016_;
v___y_2712_ = v___x_3044_;
v___y_2713_ = v___y_3020_;
v___y_2714_ = v___x_3049_;
v___y_2715_ = v___y_3036_;
v___y_2716_ = v___y_3022_;
v___y_2717_ = v___x_3043_;
v___y_2718_ = v___x_3048_;
v___y_2719_ = v___y_3026_;
v___y_2720_ = v___y_3030_;
v___y_2721_ = v___y_3031_;
v___y_2722_ = v___y_3032_;
v___y_2723_ = v___y_3033_;
v___y_2724_ = v___x_3045_;
v___y_2725_ = v___y_3034_;
v___y_2726_ = v_a_3059_;
v___y_2727_ = v_a_3057_;
v_charInst_x3f_2728_ = v___x_3074_;
v___y_2729_ = v___y_3024_;
v___y_2730_ = v___y_3025_;
v___y_2731_ = v___y_3021_;
v___y_2732_ = v___y_3027_;
v___y_2733_ = v___y_3028_;
v___y_2734_ = v___y_3029_;
v___y_2735_ = v___y_3023_;
v___y_2736_ = v___y_3019_;
v___y_2737_ = v___y_3035_;
v___y_2738_ = v___y_3017_;
goto v___jp_2706_;
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_a_3059_);
lean_dec(v_a_3057_);
lean_dec(v_a_3054_);
lean_dec_ref(v___x_3052_);
lean_dec_ref(v___x_3048_);
lean_dec(v_a_3042_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3022_);
lean_dec(v___y_3020_);
lean_dec(v___y_3018_);
lean_dec(v___y_3016_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3075_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3060_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3060_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_a_3057_);
lean_dec(v_a_3054_);
lean_dec_ref(v___x_3052_);
lean_dec_ref(v___x_3048_);
lean_dec(v_a_3042_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3022_);
lean_dec(v___y_3020_);
lean_dec(v___y_3018_);
lean_dec(v___y_3016_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3083_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3058_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3058_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_a_3054_);
lean_dec_ref(v___x_3052_);
lean_dec_ref(v___x_3048_);
lean_dec(v_a_3042_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3022_);
lean_dec(v___y_3020_);
lean_dec(v___y_3018_);
lean_dec(v___y_3016_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3091_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3056_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3056_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref(v___x_3052_);
lean_dec_ref(v___x_3048_);
lean_dec(v_a_3042_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3022_);
lean_dec(v___y_3020_);
lean_dec(v___y_3018_);
lean_dec(v___y_3016_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3099_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3053_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3053_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3022_);
lean_dec(v___y_3020_);
lean_dec(v___y_3018_);
lean_dec(v___y_3016_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3107_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3041_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3041_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3022_);
lean_dec(v___y_3020_);
lean_dec(v___y_3018_);
lean_dec(v___y_3016_);
lean_dec(v_a_3014_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3115_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3038_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3038_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec(v_a_3012_);
lean_dec(v_a_3010_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3340_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3013_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3013_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec(v_a_3010_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3348_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3011_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3011_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3356_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3009_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3009_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
v___jp_2498_:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_2524_, v___y_2532_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v_structs_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; size_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref(v___x_2534_);
v_structs_2536_ = lean_ctor_get(v_a_2535_, 0);
lean_inc_ref(v_structs_2536_);
lean_dec(v_a_2535_);
v___x_2537_ = lean_array_get_size(v_structs_2536_);
lean_dec_ref(v_structs_2536_);
v___x_2538_ = lean_unsigned_to_nat(32u);
v___x_2539_ = lean_mk_empty_array_with_capacity(v___x_2538_);
v___x_2540_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4);
v___x_2541_ = ((size_t)5ULL);
lean_inc(v___y_2512_);
v___x_2542_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2539_);
lean_ctor_set(v___x_2542_, 2, v___y_2512_);
lean_ctor_set(v___x_2542_, 3, v___y_2512_);
lean_ctor_set_usize(v___x_2542_, 4, v___x_2541_);
v___x_2543_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6);
v___x_2544_ = lean_box(0);
v___x_2545_ = lean_box(0);
lean_inc_ref_n(v___x_2542_, 7);
lean_inc(v___y_2520_);
lean_inc(v___y_2500_);
lean_inc(v___y_2521_);
lean_inc(v___y_2503_);
lean_inc(v___y_2506_);
v___x_2546_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_2546_, 0, v___x_2537_);
lean_ctor_set(v___x_2546_, 1, v_a_2486_);
lean_ctor_set(v___x_2546_, 2, v_type_2398_);
lean_ctor_set(v___x_2546_, 3, v_val_2481_);
lean_ctor_set(v___x_2546_, 4, v___y_2514_);
lean_ctor_set(v___x_2546_, 5, v_a_2492_);
lean_ctor_set(v___x_2546_, 6, v_a_2495_);
lean_ctor_set(v___x_2546_, 7, v_a_2497_);
lean_ctor_set(v___x_2546_, 8, v___y_2519_);
lean_ctor_set(v___x_2546_, 9, v___y_2504_);
lean_ctor_set(v___x_2546_, 10, v___y_2502_);
lean_ctor_set(v___x_2546_, 11, v___y_2517_);
lean_ctor_set(v___x_2546_, 12, v___y_2506_);
lean_ctor_set(v___x_2546_, 13, v___y_2516_);
lean_ctor_set(v___x_2546_, 14, v___y_2503_);
lean_ctor_set(v___x_2546_, 15, v___y_2521_);
lean_ctor_set(v___x_2546_, 16, v___y_2500_);
lean_ctor_set(v___x_2546_, 17, v___y_2510_);
lean_ctor_set(v___x_2546_, 18, v___y_2508_);
lean_ctor_set(v___x_2546_, 19, v___y_2520_);
lean_ctor_set(v___x_2546_, 20, v___y_2499_);
lean_ctor_set(v___x_2546_, 21, v___y_2501_);
lean_ctor_set(v___x_2546_, 22, v___y_2518_);
lean_ctor_set(v___x_2546_, 23, v___y_2513_);
lean_ctor_set(v___x_2546_, 24, v___y_2515_);
lean_ctor_set(v___x_2546_, 25, v___y_2511_);
lean_ctor_set(v___x_2546_, 26, v___y_2507_);
lean_ctor_set(v___x_2546_, 27, v_homomulFn_x3f_2523_);
lean_ctor_set(v___x_2546_, 28, v___y_2505_);
lean_ctor_set(v___x_2546_, 29, v___y_2522_);
lean_ctor_set(v___x_2546_, 30, v___x_2542_);
lean_ctor_set(v___x_2546_, 31, v___x_2543_);
lean_ctor_set(v___x_2546_, 32, v___x_2542_);
lean_ctor_set(v___x_2546_, 33, v___x_2542_);
lean_ctor_set(v___x_2546_, 34, v___x_2542_);
lean_ctor_set(v___x_2546_, 35, v___x_2542_);
lean_ctor_set(v___x_2546_, 36, v___x_2544_);
lean_ctor_set(v___x_2546_, 37, v___x_2543_);
lean_ctor_set(v___x_2546_, 38, v___x_2542_);
lean_ctor_set(v___x_2546_, 39, v___x_2545_);
lean_ctor_set(v___x_2546_, 40, v___x_2542_);
lean_ctor_set(v___x_2546_, 41, v___x_2542_);
lean_ctor_set_uint8(v___x_2546_, sizeof(void*)*42, v___y_2509_);
v___f_2547_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__2), 2, 1);
lean_closure_set(v___f_2547_, 0, v___x_2546_);
v___x_2548_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2549_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2548_, v___f_2547_, v___y_2524_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_dec_ref(v___x_2549_);
if (lean_obj_tag(v___y_2520_) == 1)
{
if (lean_obj_tag(v___y_2506_) == 0)
{
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2521_);
lean_dec(v___y_2503_);
lean_dec(v___y_2500_);
v___y_2411_ = v___x_2537_;
goto v___jp_2410_;
}
else
{
lean_dec_ref(v___y_2506_);
if (lean_obj_tag(v___y_2503_) == 0)
{
if (v___y_2509_ == 0)
{
if (lean_obj_tag(v___y_2521_) == 0)
{
lean_object* v_val_2550_; uint8_t v___x_2551_; 
v_val_2550_ = lean_ctor_get(v___y_2520_, 0);
lean_inc(v_val_2550_);
lean_dec_ref(v___y_2520_);
v___x_2551_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v___y_2500_);
lean_dec(v___y_2500_);
if (v___x_2551_ == 0)
{
lean_dec(v_val_2550_);
v___y_2411_ = v___x_2537_;
goto v___jp_2410_;
}
else
{
v___y_2426_ = v___y_2529_;
v___y_2427_ = v___y_2532_;
v___y_2428_ = v___y_2509_;
v___y_2429_ = v___y_2526_;
v___y_2430_ = v___y_2527_;
v___y_2431_ = v___x_2537_;
v___y_2432_ = v___y_2531_;
v___y_2433_ = v___y_2533_;
v___y_2434_ = v_val_2550_;
v___y_2435_ = v___y_2525_;
v___y_2436_ = v___y_2528_;
v___y_2437_ = v___y_2530_;
v___y_2438_ = v___y_2524_;
goto v___jp_2425_;
}
}
else
{
lean_object* v_val_2552_; 
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2500_);
v_val_2552_ = lean_ctor_get(v___y_2520_, 0);
lean_inc(v_val_2552_);
lean_dec_ref(v___y_2520_);
v___y_2426_ = v___y_2529_;
v___y_2427_ = v___y_2532_;
v___y_2428_ = v___y_2509_;
v___y_2429_ = v___y_2526_;
v___y_2430_ = v___y_2527_;
v___y_2431_ = v___x_2537_;
v___y_2432_ = v___y_2531_;
v___y_2433_ = v___y_2533_;
v___y_2434_ = v_val_2552_;
v___y_2435_ = v___y_2525_;
v___y_2436_ = v___y_2528_;
v___y_2437_ = v___y_2530_;
v___y_2438_ = v___y_2524_;
goto v___jp_2425_;
}
}
else
{
lean_object* v_val_2553_; 
lean_dec(v___y_2521_);
lean_dec(v___y_2500_);
v_val_2553_ = lean_ctor_get(v___y_2520_, 0);
lean_inc(v_val_2553_);
lean_dec_ref(v___y_2520_);
v___y_2451_ = v___y_2529_;
v___y_2452_ = v___y_2532_;
v___y_2453_ = v___y_2509_;
v___y_2454_ = v___y_2526_;
v___y_2455_ = v___y_2527_;
v___y_2456_ = v___x_2537_;
v___y_2457_ = v___y_2531_;
v___y_2458_ = v___y_2533_;
v___y_2459_ = v_val_2553_;
v___y_2460_ = v___y_2525_;
v___y_2461_ = v___y_2528_;
v___y_2462_ = v___y_2530_;
v___y_2463_ = v___y_2524_;
goto v___jp_2450_;
}
}
else
{
lean_object* v_val_2554_; 
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2521_);
lean_dec(v___y_2500_);
v_val_2554_ = lean_ctor_get(v___y_2520_, 0);
lean_inc(v_val_2554_);
lean_dec_ref(v___y_2520_);
v___y_2451_ = v___y_2529_;
v___y_2452_ = v___y_2532_;
v___y_2453_ = v___y_2509_;
v___y_2454_ = v___y_2526_;
v___y_2455_ = v___y_2527_;
v___y_2456_ = v___x_2537_;
v___y_2457_ = v___y_2531_;
v___y_2458_ = v___y_2533_;
v___y_2459_ = v_val_2554_;
v___y_2460_ = v___y_2525_;
v___y_2461_ = v___y_2528_;
v___y_2462_ = v___y_2530_;
v___y_2463_ = v___y_2524_;
goto v___jp_2450_;
}
}
}
else
{
lean_dec(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec(v___y_2506_);
lean_dec(v___y_2503_);
lean_dec(v___y_2500_);
v___y_2411_ = v___x_2537_;
goto v___jp_2410_;
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec(v___y_2506_);
lean_dec(v___y_2503_);
lean_dec(v___y_2500_);
v_a_2555_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2549_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2549_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v_homomulFn_x3f_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_dec(v_a_2486_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2563_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2534_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2534_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
v___jp_2571_:
{
lean_object* v___x_2606_; 
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2606_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(v_val_2481_, v_type_2398_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2608_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2606_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2608_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(v_val_2481_, v_type_2398_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
if (lean_obj_tag(v___x_2608_) == 0)
{
if (lean_obj_tag(v___y_2588_) == 0)
{
lean_object* v_a_2609_; 
lean_dec(v___y_2583_);
lean_del_object(v___x_2483_);
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref(v___x_2608_);
v___y_2499_ = v___y_2573_;
v___y_2500_ = v___y_2574_;
v___y_2501_ = v_ltFn_x3f_2595_;
v___y_2502_ = v___y_2575_;
v___y_2503_ = v___y_2576_;
v___y_2504_ = v___y_2577_;
v___y_2505_ = v___y_2578_;
v___y_2506_ = v___y_2579_;
v___y_2507_ = v_a_2609_;
v___y_2508_ = v___y_2580_;
v___y_2509_ = v___y_2581_;
v___y_2510_ = v___y_2582_;
v___y_2511_ = v_a_2607_;
v___y_2512_ = v___y_2584_;
v___y_2513_ = v___y_2585_;
v___y_2514_ = v___y_2586_;
v___y_2515_ = v___y_2587_;
v___y_2516_ = v___y_2588_;
v___y_2517_ = v___y_2589_;
v___y_2518_ = v___y_2590_;
v___y_2519_ = v___y_2591_;
v___y_2520_ = v___y_2592_;
v___y_2521_ = v___y_2593_;
v___y_2522_ = v___y_2594_;
v_homomulFn_x3f_2523_ = v___y_2572_;
v___y_2524_ = v___y_2596_;
v___y_2525_ = v___y_2597_;
v___y_2526_ = v___y_2598_;
v___y_2527_ = v___y_2599_;
v___y_2528_ = v___y_2600_;
v___y_2529_ = v___y_2601_;
v___y_2530_ = v___y_2602_;
v___y_2531_ = v___y_2603_;
v___y_2532_ = v___y_2604_;
v___y_2533_ = v___y_2605_;
goto v___jp_2498_;
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
lean_dec(v___y_2572_);
v_a_2610_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2610_);
lean_dec_ref(v___x_2608_);
v___x_2611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8));
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2612_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v___x_2611_, v_val_2481_, v_type_2398_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref(v___x_2612_);
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10));
v___x_2615_ = l_Lean_mkConst(v___x_2614_, v___y_2583_);
lean_inc_ref_n(v_type_2398_, 3);
v___x_2616_ = l_Lean_mkApp4(v___x_2615_, v_type_2398_, v_type_2398_, v_type_2398_, v_a_2613_);
v___x_2617_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_2616_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2620_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2617_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v_a_2618_);
v___x_2620_ = v___x_2483_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
v___y_2499_ = v___y_2573_;
v___y_2500_ = v___y_2574_;
v___y_2501_ = v_ltFn_x3f_2595_;
v___y_2502_ = v___y_2575_;
v___y_2503_ = v___y_2576_;
v___y_2504_ = v___y_2577_;
v___y_2505_ = v___y_2578_;
v___y_2506_ = v___y_2579_;
v___y_2507_ = v_a_2610_;
v___y_2508_ = v___y_2580_;
v___y_2509_ = v___y_2581_;
v___y_2510_ = v___y_2582_;
v___y_2511_ = v_a_2607_;
v___y_2512_ = v___y_2584_;
v___y_2513_ = v___y_2585_;
v___y_2514_ = v___y_2586_;
v___y_2515_ = v___y_2587_;
v___y_2516_ = v___y_2588_;
v___y_2517_ = v___y_2589_;
v___y_2518_ = v___y_2590_;
v___y_2519_ = v___y_2591_;
v___y_2520_ = v___y_2592_;
v___y_2521_ = v___y_2593_;
v___y_2522_ = v___y_2594_;
v_homomulFn_x3f_2523_ = v___x_2620_;
v___y_2524_ = v___y_2596_;
v___y_2525_ = v___y_2597_;
v___y_2526_ = v___y_2598_;
v___y_2527_ = v___y_2599_;
v___y_2528_ = v___y_2600_;
v___y_2529_ = v___y_2601_;
v___y_2530_ = v___y_2602_;
v___y_2531_ = v___y_2603_;
v___y_2532_ = v___y_2604_;
v___y_2533_ = v___y_2605_;
goto v___jp_2498_;
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec_ref(v___y_2588_);
lean_dec(v_a_2610_);
lean_dec(v_a_2607_);
lean_dec(v_ltFn_x3f_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2622_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2617_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2617_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec_ref(v___y_2588_);
lean_dec(v_a_2610_);
lean_dec(v_a_2607_);
lean_dec(v_ltFn_x3f_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2630_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2612_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2612_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_a_2607_);
lean_dec(v_ltFn_x3f_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2638_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2608_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2608_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_ltFn_x3f_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2646_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2606_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2606_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
v___jp_2654_:
{
if (lean_obj_tag(v_a_2495_) == 1)
{
lean_object* v_val_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_val_2689_ = lean_ctor_get(v_a_2495_, 0);
v___x_2690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12));
v___x_2691_ = l_Lean_mkConst(v___x_2690_, v___y_2659_);
lean_inc(v_val_2689_);
lean_inc_ref(v_type_2398_);
v___x_2692_ = l_Lean_mkAppB(v___x_2691_, v_type_2398_, v_val_2689_);
v___x_2693_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_2692_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref(v___x_2693_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set_tag(v___x_2488_, 1);
lean_ctor_set(v___x_2488_, 0, v_a_2694_);
v___x_2696_ = v___x_2488_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
v___y_2572_ = v___y_2655_;
v___y_2573_ = v_leFn_x3f_2678_;
v___y_2574_ = v___y_2656_;
v___y_2575_ = v___y_2657_;
v___y_2576_ = v___y_2658_;
v___y_2577_ = v___y_2660_;
v___y_2578_ = v___y_2661_;
v___y_2579_ = v___y_2662_;
v___y_2580_ = v___y_2663_;
v___y_2581_ = v___y_2664_;
v___y_2582_ = v___y_2665_;
v___y_2583_ = v___y_2666_;
v___y_2584_ = v___y_2667_;
v___y_2585_ = v___y_2668_;
v___y_2586_ = v___y_2669_;
v___y_2587_ = v___y_2670_;
v___y_2588_ = v___y_2671_;
v___y_2589_ = v___y_2672_;
v___y_2590_ = v___y_2673_;
v___y_2591_ = v___y_2674_;
v___y_2592_ = v___y_2675_;
v___y_2593_ = v___y_2676_;
v___y_2594_ = v___y_2677_;
v_ltFn_x3f_2595_ = v___x_2696_;
v___y_2596_ = v___y_2679_;
v___y_2597_ = v___y_2680_;
v___y_2598_ = v___y_2681_;
v___y_2599_ = v___y_2682_;
v___y_2600_ = v___y_2683_;
v___y_2601_ = v___y_2684_;
v___y_2602_ = v___y_2685_;
v___y_2603_ = v___y_2686_;
v___y_2604_ = v___y_2687_;
v___y_2605_ = v___y_2688_;
goto v___jp_2571_;
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec_ref(v_a_2495_);
lean_dec(v_leFn_x3f_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec(v_a_2497_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2698_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2693_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2693_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_dec(v___y_2659_);
lean_del_object(v___x_2488_);
lean_inc(v___y_2655_);
v___y_2572_ = v___y_2655_;
v___y_2573_ = v_leFn_x3f_2678_;
v___y_2574_ = v___y_2656_;
v___y_2575_ = v___y_2657_;
v___y_2576_ = v___y_2658_;
v___y_2577_ = v___y_2660_;
v___y_2578_ = v___y_2661_;
v___y_2579_ = v___y_2662_;
v___y_2580_ = v___y_2663_;
v___y_2581_ = v___y_2664_;
v___y_2582_ = v___y_2665_;
v___y_2583_ = v___y_2666_;
v___y_2584_ = v___y_2667_;
v___y_2585_ = v___y_2668_;
v___y_2586_ = v___y_2669_;
v___y_2587_ = v___y_2670_;
v___y_2588_ = v___y_2671_;
v___y_2589_ = v___y_2672_;
v___y_2590_ = v___y_2673_;
v___y_2591_ = v___y_2674_;
v___y_2592_ = v___y_2675_;
v___y_2593_ = v___y_2676_;
v___y_2594_ = v___y_2677_;
v_ltFn_x3f_2595_ = v___y_2655_;
v___y_2596_ = v___y_2679_;
v___y_2597_ = v___y_2680_;
v___y_2598_ = v___y_2681_;
v___y_2599_ = v___y_2682_;
v___y_2600_ = v___y_2683_;
v___y_2601_ = v___y_2684_;
v___y_2602_ = v___y_2685_;
v___y_2603_ = v___y_2686_;
v___y_2604_ = v___y_2687_;
v___y_2605_ = v___y_2688_;
goto v___jp_2571_;
}
}
v___jp_2706_:
{
lean_object* v___x_2739_; 
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2739_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_val_2481_, v_type_2398_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref(v___x_2739_);
v___x_2741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14));
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2742_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v___x_2741_, v_val_2481_, v_type_2398_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref(v___x_2742_);
v___x_2744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16));
lean_inc(v___y_2710_);
v___x_2745_ = l_Lean_mkConst(v___x_2744_, v___y_2710_);
lean_inc(v_a_2743_);
lean_inc_ref(v_type_2398_);
v___x_2746_ = l_Lean_mkAppB(v___x_2745_, v_type_2398_, v_a_2743_);
v___x_2747_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_2746_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref(v___x_2747_);
v___x_2749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18));
lean_inc(v___y_2710_);
v___x_2750_ = l_Lean_mkConst(v___x_2749_, v___y_2710_);
v___x_2751_ = lean_unsigned_to_nat(0u);
v___x_2752_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19);
lean_inc_ref(v_type_2398_);
v___x_2753_ = l_Lean_mkAppB(v___x_2750_, v_type_2398_, v___x_2752_);
v___x_2754_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_2753_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2976_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2976_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2976_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
if (lean_obj_tag(v_a_2755_) == 1)
{
lean_object* v_val_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2971_; 
lean_del_object(v___x_2757_);
v_val_2759_ = lean_ctor_get(v_a_2755_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_a_2755_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2761_ = v_a_2755_;
v_isShared_2762_ = v_isSharedCheck_2971_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_val_2759_);
lean_dec(v_a_2755_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2971_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21));
lean_inc(v___y_2710_);
v___x_2764_ = l_Lean_mkConst(v___x_2763_, v___y_2710_);
lean_inc_ref(v_type_2398_);
v___x_2765_ = l_Lean_mkApp3(v___x_2764_, v_type_2398_, v___x_2752_, v_val_2759_);
v___x_2766_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_2765_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2768_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref(v___x_2766_);
lean_inc(v_a_2767_);
lean_inc(v_a_2748_);
v___x_2768_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_2748_, v_a_2767_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec_ref(v___x_2768_);
v___x_2769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23));
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2770_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v___x_2769_, v_val_2481_, v_type_2398_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref(v___x_2770_);
v___x_2772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25));
lean_inc(v___y_2716_);
v___x_2773_ = l_Lean_mkConst(v___x_2772_, v___y_2716_);
lean_inc(v_a_2771_);
lean_inc_ref_n(v_type_2398_, 3);
v___x_2774_ = l_Lean_mkApp4(v___x_2773_, v_type_2398_, v_type_2398_, v_type_2398_, v_a_2771_);
v___x_2775_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_2774_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref(v___x_2775_);
v___x_2777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27));
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2778_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v___x_2777_, v_val_2481_, v_type_2398_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref(v___x_2778_);
v___x_2780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29));
lean_inc(v___y_2710_);
v___x_2781_ = l_Lean_mkConst(v___x_2780_, v___y_2710_);
lean_inc(v_a_2779_);
lean_inc_ref(v_type_2398_);
v___x_2782_ = l_Lean_mkAppB(v___x_2781_, v_type_2398_, v_a_2779_);
v___x_2783_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_2782_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref(v___x_2783_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(v_val_2481_, v_type_2398_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref(v___x_2785_);
v___x_2787_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
v___x_2788_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2);
v___x_2789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v___y_2725_);
v___x_2790_ = l_Lean_mkConst(v___x_2787_, v___x_2789_);
v___x_2791_ = l_Lean_Int_mkType;
lean_inc(v_a_2786_);
lean_inc_ref_n(v_type_2398_, 2);
lean_inc_ref(v___x_2790_);
v___x_2792_ = l_Lean_mkApp4(v___x_2790_, v___x_2791_, v_type_2398_, v_type_2398_, v_a_2786_);
v___x_2793_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_2792_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2795_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref(v___x_2793_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2795_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_val_2481_, v_type_2398_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref(v___x_2795_);
v___x_2797_ = l_Lean_Nat_mkType;
lean_inc(v_a_2796_);
lean_inc_ref_n(v_type_2398_, 2);
v___x_2798_ = l_Lean_mkApp4(v___x_2790_, v___x_2797_, v_type_2398_, v_type_2398_, v_a_2796_);
v___x_2799_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_2798_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref(v___x_2799_);
v___x_2801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30));
v___x_2802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31));
lean_inc_ref(v___y_2712_);
lean_inc_ref(v___y_2717_);
v___x_2803_ = l_Lean_Name_mkStr4(v___y_2717_, v___y_2712_, v___x_2801_, v___x_2802_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
lean_inc_ref(v___y_2707_);
v___x_2804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2743_, v___y_2707_, v___x_2803_, v_val_2481_, v_type_2398_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
lean_dec_ref(v___x_2804_);
v___x_2805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32));
lean_inc_ref(v___y_2712_);
lean_inc_ref(v___y_2717_);
v___x_2806_ = l_Lean_Name_mkStr4(v___y_2717_, v___y_2712_, v___x_2801_, v___x_2805_);
v___x_2807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34));
v___x_2808_ = lean_box(0);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v___y_2722_, v___y_2707_, v___x_2806_, v___x_2807_, v_val_2481_, v_type_2398_, v___x_2808_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_dec_ref(v___x_2809_);
v___x_2810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35));
lean_inc_ref(v___y_2714_);
lean_inc_ref(v___y_2712_);
lean_inc_ref(v___y_2717_);
v___x_2811_ = l_Lean_Name_mkStr4(v___y_2717_, v___y_2712_, v___y_2714_, v___x_2810_);
v___x_2812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37));
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
lean_inc_ref(v___y_2718_);
v___x_2813_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2771_, v___y_2718_, v___x_2811_, v___x_2812_, v_val_2481_, v_type_2398_, v___x_2808_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_dec_ref(v___x_2813_);
v___x_2814_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38));
lean_inc_ref(v___y_2714_);
lean_inc_ref(v___y_2712_);
lean_inc_ref(v___y_2717_);
v___x_2815_ = l_Lean_Name_mkStr4(v___y_2717_, v___y_2712_, v___y_2714_, v___x_2814_);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
v___x_2816_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2779_, v___y_2718_, v___x_2815_, v_val_2481_, v_type_2398_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
lean_dec_ref(v___x_2816_);
v___x_2817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39));
lean_inc_ref(v___y_2724_);
lean_inc_ref(v___y_2712_);
lean_inc_ref(v___y_2717_);
v___x_2818_ = l_Lean_Name_mkStr4(v___y_2717_, v___y_2712_, v___y_2724_, v___x_2817_);
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41));
v___x_2820_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
lean_inc_ref(v___y_2719_);
v___x_2821_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2786_, v___y_2719_, v___x_2818_, v___x_2819_, v_val_2481_, v_type_2398_, v___x_2820_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec_ref(v___x_2821_);
v___x_2822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43));
lean_inc_ref(v___y_2724_);
lean_inc_ref(v___y_2712_);
lean_inc_ref(v___y_2717_);
v___x_2823_ = l_Lean_Name_mkStr4(v___y_2717_, v___y_2712_, v___y_2724_, v___x_2822_);
v___x_2824_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44);
lean_inc_ref(v_type_2398_);
lean_inc(v_val_2481_);
lean_inc_ref(v___y_2719_);
v___x_2825_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2796_, v___y_2719_, v___x_2823_, v___x_2819_, v_val_2481_, v_type_2398_, v___x_2824_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_dec_ref(v___x_2825_);
if (lean_obj_tag(v_a_2492_) == 1)
{
lean_object* v_val_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_val_2826_ = lean_ctor_get(v_a_2492_, 0);
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46));
lean_inc(v___y_2710_);
v___x_2828_ = l_Lean_mkConst(v___x_2827_, v___y_2710_);
lean_inc(v_val_2826_);
lean_inc_ref(v_type_2398_);
v___x_2829_ = l_Lean_mkAppB(v___x_2828_, v_type_2398_, v_val_2826_);
v___x_2830_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_2829_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v___x_2830_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v_a_2831_);
v___x_2833_ = v___x_2761_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
v___y_2655_ = v___x_2808_;
v___y_2656_ = v_charInst_x3f_2728_;
v___y_2657_ = v___y_2708_;
v___y_2658_ = v___y_2709_;
v___y_2659_ = v___y_2710_;
v___y_2660_ = v___y_2711_;
v___y_2661_ = v_a_2776_;
v___y_2662_ = v___y_2713_;
v___y_2663_ = v_a_2767_;
v___y_2664_ = v___y_2715_;
v___y_2665_ = v_a_2748_;
v___y_2666_ = v___y_2716_;
v___y_2667_ = v___x_2751_;
v___y_2668_ = v_a_2794_;
v___y_2669_ = v___y_2719_;
v___y_2670_ = v_a_2800_;
v___y_2671_ = v___y_2720_;
v___y_2672_ = v_a_2740_;
v___y_2673_ = v___y_2721_;
v___y_2674_ = v___y_2723_;
v___y_2675_ = v___y_2726_;
v___y_2676_ = v___y_2727_;
v___y_2677_ = v_a_2784_;
v_leFn_x3f_2678_ = v___x_2833_;
v___y_2679_ = v___y_2729_;
v___y_2680_ = v___y_2730_;
v___y_2681_ = v___y_2731_;
v___y_2682_ = v___y_2732_;
v___y_2683_ = v___y_2733_;
v___y_2684_ = v___y_2734_;
v___y_2685_ = v___y_2735_;
v___y_2686_ = v___y_2736_;
v___y_2687_ = v___y_2737_;
v___y_2688_ = v___y_2738_;
goto v___jp_2654_;
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2800_);
lean_dec(v_a_2794_);
lean_dec(v_a_2784_);
lean_dec(v_a_2776_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2835_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2830_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2830_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_del_object(v___x_2761_);
v___y_2655_ = v___x_2808_;
v___y_2656_ = v_charInst_x3f_2728_;
v___y_2657_ = v___y_2708_;
v___y_2658_ = v___y_2709_;
v___y_2659_ = v___y_2710_;
v___y_2660_ = v___y_2711_;
v___y_2661_ = v_a_2776_;
v___y_2662_ = v___y_2713_;
v___y_2663_ = v_a_2767_;
v___y_2664_ = v___y_2715_;
v___y_2665_ = v_a_2748_;
v___y_2666_ = v___y_2716_;
v___y_2667_ = v___x_2751_;
v___y_2668_ = v_a_2794_;
v___y_2669_ = v___y_2719_;
v___y_2670_ = v_a_2800_;
v___y_2671_ = v___y_2720_;
v___y_2672_ = v_a_2740_;
v___y_2673_ = v___y_2721_;
v___y_2674_ = v___y_2723_;
v___y_2675_ = v___y_2726_;
v___y_2676_ = v___y_2727_;
v___y_2677_ = v_a_2784_;
v_leFn_x3f_2678_ = v___x_2808_;
v___y_2679_ = v___y_2729_;
v___y_2680_ = v___y_2730_;
v___y_2681_ = v___y_2731_;
v___y_2682_ = v___y_2732_;
v___y_2683_ = v___y_2733_;
v___y_2684_ = v___y_2734_;
v___y_2685_ = v___y_2735_;
v___y_2686_ = v___y_2736_;
v___y_2687_ = v___y_2737_;
v___y_2688_ = v___y_2738_;
goto v___jp_2654_;
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v_a_2800_);
lean_dec(v_a_2794_);
lean_dec(v_a_2784_);
lean_dec(v_a_2776_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2843_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2825_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2825_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v_a_2800_);
lean_dec(v_a_2796_);
lean_dec(v_a_2794_);
lean_dec(v_a_2784_);
lean_dec(v_a_2776_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2851_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2821_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2821_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec(v_a_2800_);
lean_dec(v_a_2796_);
lean_dec(v_a_2794_);
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
lean_dec(v_a_2776_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2859_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2816_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2816_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v_a_2800_);
lean_dec(v_a_2796_);
lean_dec(v_a_2794_);
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
lean_dec(v_a_2779_);
lean_dec(v_a_2776_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2867_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2813_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2813_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec(v_a_2800_);
lean_dec(v_a_2796_);
lean_dec(v_a_2794_);
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
lean_dec(v_a_2779_);
lean_dec(v_a_2776_);
lean_dec(v_a_2771_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2875_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2809_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2809_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec(v_a_2800_);
lean_dec(v_a_2796_);
lean_dec(v_a_2794_);
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
lean_dec(v_a_2779_);
lean_dec(v_a_2776_);
lean_dec(v_a_2771_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2883_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2804_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2804_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v_a_2796_);
lean_dec(v_a_2794_);
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
lean_dec(v_a_2779_);
lean_dec(v_a_2776_);
lean_dec(v_a_2771_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2891_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2799_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2799_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_a_2794_);
lean_dec_ref(v___x_2790_);
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
lean_dec(v_a_2779_);
lean_dec(v_a_2776_);
lean_dec(v_a_2771_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2899_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2795_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2795_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec_ref(v___x_2790_);
lean_dec(v_a_2786_);
lean_dec(v_a_2784_);
lean_dec(v_a_2779_);
lean_dec(v_a_2776_);
lean_dec(v_a_2771_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2907_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2793_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2793_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v_a_2784_);
lean_dec(v_a_2779_);
lean_dec(v_a_2776_);
lean_dec(v_a_2771_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2915_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2785_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2785_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v_a_2779_);
lean_dec(v_a_2776_);
lean_dec(v_a_2771_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2923_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2783_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2783_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec(v_a_2776_);
lean_dec(v_a_2771_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2931_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2778_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2778_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec(v_a_2771_);
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2939_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2775_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2775_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2947_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2770_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2770_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec(v_a_2767_);
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2955_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2768_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2768_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_del_object(v___x_2761_);
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2963_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2766_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2766_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_dec(v_a_2755_);
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v___x_2972_ = lean_box(0);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2972_);
v___x_2974_ = v___x_2757_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec(v_a_2748_);
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2977_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2754_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2754_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec(v_a_2743_);
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2985_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2747_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2747_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v_a_2740_);
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_2993_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2742_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2742_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec(v_charInst_x3f_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2716_);
lean_dec(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_a_2497_);
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3001_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2739_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2739_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_dec(v_a_2495_);
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3364_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_2496_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_2496_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_dec(v_a_2492_);
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3372_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_2494_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_2494_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_del_object(v___x_2488_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
v_a_3380_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_2491_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_2491_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
}
else
{
lean_del_object(v___x_2483_);
lean_dec(v_val_2481_);
lean_dec_ref(v_type_2398_);
return v___x_2485_;
}
}
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
lean_dec(v_a_2477_);
lean_dec_ref(v_type_2398_);
v___x_3390_ = lean_box(0);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v___x_3390_);
v___x_3392_ = v___x_2479_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec_ref(v_type_2398_);
v_a_3395_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_2476_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_2476_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
v___jp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___y_2411_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
v___jp_2414_:
{
if (lean_obj_tag(v___y_2416_) == 0)
{
lean_dec_ref(v___y_2416_);
v___y_2411_ = v___y_2415_;
goto v___jp_2410_;
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v___y_2415_);
v_a_2417_ = lean_ctor_get(v___y_2416_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___y_2416_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___y_2416_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___y_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
v___jp_2425_:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2434_, v___y_2428_, v___y_2431_, v___y_2438_, v___y_2435_, v___y_2429_, v___y_2430_, v___y_2436_, v___y_2426_, v___y_2437_, v___y_2432_, v___y_2427_, v___y_2433_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2441_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref(v___x_2439_);
v___x_2441_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2440_, v___y_2431_, v___y_2438_);
v___y_2415_ = v___y_2431_;
v___y_2416_ = v___x_2441_;
goto v___jp_2414_;
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v___y_2431_);
v_a_2442_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2439_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2439_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
v___jp_2450_:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2459_, v___y_2453_, v___y_2456_, v___y_2463_, v___y_2460_, v___y_2454_, v___y_2455_, v___y_2461_, v___y_2451_, v___y_2462_, v___y_2457_, v___y_2452_, v___y_2458_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2466_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v___x_2464_);
lean_inc(v_a_2465_);
v___x_2466_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_a_2465_, v___y_2456_, v___y_2463_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v___x_2467_; 
lean_dec_ref(v___x_2466_);
v___x_2467_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2465_, v___y_2456_, v___y_2463_);
v___y_2415_ = v___y_2456_;
v___y_2416_ = v___x_2467_;
goto v___jp_2414_;
}
else
{
lean_dec(v_a_2465_);
v___y_2415_ = v___y_2456_;
v___y_2416_ = v___x_2466_;
goto v___jp_2414_;
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v___y_2456_);
v_a_2468_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2464_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2464_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object* v_type_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
lean_dec(v_a_3413_);
lean_dec_ref(v_a_3412_);
lean_dec(v_a_3411_);
lean_dec_ref(v_a_3410_);
lean_dec(v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec(v_a_3404_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b2_3416_, lean_object* v_x_3417_, lean_object* v_x_3418_, lean_object* v_x_3419_){
_start:
{
lean_object* v___x_3420_; 
v___x_3420_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(v_x_3417_, v_x_3418_, v_x_3419_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3421_, lean_object* v_x_3422_, size_t v_x_3423_, size_t v_x_3424_, lean_object* v_x_3425_, lean_object* v_x_3426_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(v_x_3422_, v_x_3423_, v_x_3424_, v_x_3425_, v_x_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3428_, lean_object* v_x_3429_, lean_object* v_x_3430_, lean_object* v_x_3431_, lean_object* v_x_3432_, lean_object* v_x_3433_){
_start:
{
size_t v_x_577323__boxed_3434_; size_t v_x_577324__boxed_3435_; lean_object* v_res_3436_; 
v_x_577323__boxed_3434_ = lean_unbox_usize(v_x_3430_);
lean_dec(v_x_3430_);
v_x_577324__boxed_3435_ = lean_unbox_usize(v_x_3431_);
lean_dec(v_x_3431_);
v_res_3436_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0(v_00_u03b2_3428_, v_x_3429_, v_x_577323__boxed_3434_, v_x_577324__boxed_3435_, v_x_3432_, v_x_3433_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3437_, lean_object* v_n_3438_, lean_object* v_k_3439_, lean_object* v_v_3440_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(v_n_3438_, v_k_3439_, v_v_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3442_, size_t v_depth_3443_, lean_object* v_keys_3444_, lean_object* v_vals_3445_, lean_object* v_heq_3446_, lean_object* v_i_3447_, lean_object* v_entries_3448_){
_start:
{
lean_object* v___x_3449_; 
v___x_3449_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(v_depth_3443_, v_keys_3444_, v_vals_3445_, v_i_3447_, v_entries_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3450_, lean_object* v_depth_3451_, lean_object* v_keys_3452_, lean_object* v_vals_3453_, lean_object* v_heq_3454_, lean_object* v_i_3455_, lean_object* v_entries_3456_){
_start:
{
size_t v_depth_boxed_3457_; lean_object* v_res_3458_; 
v_depth_boxed_3457_ = lean_unbox_usize(v_depth_3451_);
lean_dec(v_depth_3451_);
v_res_3458_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2(v_00_u03b2_3450_, v_depth_boxed_3457_, v_keys_3452_, v_vals_3453_, v_heq_3454_, v_i_3455_, v_entries_3456_);
lean_dec_ref(v_vals_3453_);
lean_dec_ref(v_keys_3452_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3459_, lean_object* v_x_3460_, lean_object* v_x_3461_, lean_object* v_x_3462_, lean_object* v_x_3463_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3460_, v_x_3461_, v_x_3462_, v_x_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object* v_type_3465_, lean_object* v_a_3466_, lean_object* v_s_3467_){
_start:
{
lean_object* v_structs_3468_; lean_object* v_typeIdOf_3469_; lean_object* v_exprToStructId_3470_; lean_object* v_exprToStructIdEntries_3471_; lean_object* v_forbiddenNatModules_3472_; lean_object* v_natStructs_3473_; lean_object* v_natTypeIdOf_3474_; lean_object* v_exprToNatStructId_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3483_; 
v_structs_3468_ = lean_ctor_get(v_s_3467_, 0);
v_typeIdOf_3469_ = lean_ctor_get(v_s_3467_, 1);
v_exprToStructId_3470_ = lean_ctor_get(v_s_3467_, 2);
v_exprToStructIdEntries_3471_ = lean_ctor_get(v_s_3467_, 3);
v_forbiddenNatModules_3472_ = lean_ctor_get(v_s_3467_, 4);
v_natStructs_3473_ = lean_ctor_get(v_s_3467_, 5);
v_natTypeIdOf_3474_ = lean_ctor_get(v_s_3467_, 6);
v_exprToNatStructId_3475_ = lean_ctor_get(v_s_3467_, 7);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_s_3467_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3477_ = v_s_3467_;
v_isShared_3478_ = v_isSharedCheck_3483_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_exprToNatStructId_3475_);
lean_inc(v_natTypeIdOf_3474_);
lean_inc(v_natStructs_3473_);
lean_inc(v_forbiddenNatModules_3472_);
lean_inc(v_exprToStructIdEntries_3471_);
lean_inc(v_exprToStructId_3470_);
lean_inc(v_typeIdOf_3469_);
lean_inc(v_structs_3468_);
lean_dec(v_s_3467_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3483_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___x_3479_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(v_typeIdOf_3469_, v_type_3465_, v_a_3466_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 1, v___x_3479_);
v___x_3481_ = v___x_3477_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_structs_3468_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v_exprToStructId_3470_);
lean_ctor_set(v_reuseFailAlloc_3482_, 3, v_exprToStructIdEntries_3471_);
lean_ctor_set(v_reuseFailAlloc_3482_, 4, v_forbiddenNatModules_3472_);
lean_ctor_set(v_reuseFailAlloc_3482_, 5, v_natStructs_3473_);
lean_ctor_set(v_reuseFailAlloc_3482_, 6, v_natTypeIdOf_3474_);
lean_ctor_set(v_reuseFailAlloc_3482_, 7, v_exprToNatStructId_3475_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3484_, lean_object* v_vals_3485_, lean_object* v_i_3486_, lean_object* v_k_3487_){
_start:
{
lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3488_ = lean_array_get_size(v_keys_3484_);
v___x_3489_ = lean_nat_dec_lt(v_i_3486_, v___x_3488_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; 
lean_dec(v_i_3486_);
v___x_3490_ = lean_box(0);
return v___x_3490_;
}
else
{
lean_object* v_k_x27_3491_; uint8_t v___x_3492_; 
v_k_x27_3491_ = lean_array_fget_borrowed(v_keys_3484_, v_i_3486_);
v___x_3492_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_3487_, v_k_x27_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = lean_unsigned_to_nat(1u);
v___x_3494_ = lean_nat_add(v_i_3486_, v___x_3493_);
lean_dec(v_i_3486_);
v_i_3486_ = v___x_3494_;
goto _start;
}
else
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = lean_array_fget_borrowed(v_vals_3485_, v_i_3486_);
lean_dec(v_i_3486_);
lean_inc(v___x_3496_);
v___x_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
return v___x_3497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3498_, lean_object* v_vals_3499_, lean_object* v_i_3500_, lean_object* v_k_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3498_, v_vals_3499_, v_i_3500_, v_k_3501_);
lean_dec_ref(v_k_3501_);
lean_dec_ref(v_vals_3499_);
lean_dec_ref(v_keys_3498_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_3503_, size_t v_x_3504_, lean_object* v_x_3505_){
_start:
{
if (lean_obj_tag(v_x_3503_) == 0)
{
lean_object* v_es_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3527_; 
v_es_3506_ = lean_ctor_get(v_x_3503_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_x_3503_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3508_ = v_x_3503_;
v_isShared_3509_ = v_isSharedCheck_3527_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_es_3506_);
lean_dec(v_x_3503_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3527_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; size_t v___x_3511_; size_t v___x_3512_; size_t v___x_3513_; lean_object* v_j_3514_; lean_object* v___x_3515_; 
v___x_3510_ = lean_box(2);
v___x_3511_ = ((size_t)5ULL);
v___x_3512_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1);
v___x_3513_ = lean_usize_land(v_x_3504_, v___x_3512_);
v_j_3514_ = lean_usize_to_nat(v___x_3513_);
v___x_3515_ = lean_array_get(v___x_3510_, v_es_3506_, v_j_3514_);
lean_dec(v_j_3514_);
lean_dec_ref(v_es_3506_);
switch(lean_obj_tag(v___x_3515_))
{
case 0:
{
lean_object* v_key_3516_; lean_object* v_val_3517_; uint8_t v___x_3518_; 
v_key_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_key_3516_);
v_val_3517_ = lean_ctor_get(v___x_3515_, 1);
lean_inc(v_val_3517_);
lean_dec_ref(v___x_3515_);
v___x_3518_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3505_, v_key_3516_);
lean_dec(v_key_3516_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; 
lean_dec(v_val_3517_);
lean_del_object(v___x_3508_);
v___x_3519_ = lean_box(0);
return v___x_3519_;
}
else
{
lean_object* v___x_3521_; 
if (v_isShared_3509_ == 0)
{
lean_ctor_set_tag(v___x_3508_, 1);
lean_ctor_set(v___x_3508_, 0, v_val_3517_);
v___x_3521_ = v___x_3508_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_val_3517_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
case 1:
{
lean_object* v_node_3523_; size_t v___x_3524_; 
lean_del_object(v___x_3508_);
v_node_3523_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_node_3523_);
lean_dec_ref(v___x_3515_);
v___x_3524_ = lean_usize_shift_right(v_x_3504_, v___x_3511_);
v_x_3503_ = v_node_3523_;
v_x_3504_ = v___x_3524_;
goto _start;
}
default: 
{
lean_object* v___x_3526_; 
lean_del_object(v___x_3508_);
v___x_3526_ = lean_box(0);
return v___x_3526_;
}
}
}
}
else
{
lean_object* v_ks_3528_; lean_object* v_vs_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v_ks_3528_ = lean_ctor_get(v_x_3503_, 0);
lean_inc_ref(v_ks_3528_);
v_vs_3529_ = lean_ctor_get(v_x_3503_, 1);
lean_inc_ref(v_vs_3529_);
lean_dec_ref(v_x_3503_);
v___x_3530_ = lean_unsigned_to_nat(0u);
v___x_3531_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_3528_, v_vs_3529_, v___x_3530_, v_x_3505_);
lean_dec_ref(v_vs_3529_);
lean_dec_ref(v_ks_3528_);
return v___x_3531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_3532_, lean_object* v_x_3533_, lean_object* v_x_3534_){
_start:
{
size_t v_x_7996__boxed_3535_; lean_object* v_res_3536_; 
v_x_7996__boxed_3535_ = lean_unbox_usize(v_x_3533_);
lean_dec(v_x_3533_);
v_res_3536_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_3532_, v_x_7996__boxed_3535_, v_x_3534_);
lean_dec_ref(v_x_3534_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object* v_x_3537_, lean_object* v_x_3538_){
_start:
{
uint64_t v___x_3539_; size_t v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3538_);
v___x_3540_ = lean_uint64_to_usize(v___x_3539_);
v___x_3541_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_3537_, v___x_3540_, v_x_3538_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_3542_, lean_object* v_x_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_3542_, v_x_3543_);
lean_dec_ref(v_x_3543_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object* v_type_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3548_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3627_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3560_ = v___x_3557_;
v_isShared_3561_ = v_isSharedCheck_3627_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3557_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3627_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
uint8_t v_linarith_3562_; 
v_linarith_3562_ = lean_ctor_get_uint8(v_a_3558_, sizeof(void*)*11 + 22);
lean_dec(v_a_3558_);
if (v_linarith_3562_ == 0)
{
lean_object* v___x_3563_; lean_object* v___x_3565_; 
lean_dec_ref(v_type_3545_);
v___x_3563_ = lean_box(0);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3563_);
v___x_3565_ = v___x_3560_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
else
{
lean_object* v___x_3567_; 
lean_del_object(v___x_3560_);
lean_inc_ref(v_type_3545_);
v___x_3567_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3618_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3618_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3618_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
uint8_t v___x_3572_; 
v___x_3572_ = lean_unbox(v_a_3568_);
lean_dec(v_a_3568_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3573_; 
lean_del_object(v___x_3570_);
v___x_3573_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_3546_, v_a_3554_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3605_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3576_ = v___x_3573_;
v_isShared_3577_ = v_isSharedCheck_3605_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3573_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3605_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v_typeIdOf_3578_; lean_object* v___x_3579_; 
v_typeIdOf_3578_ = lean_ctor_get(v_a_3574_, 1);
lean_inc_ref(v_typeIdOf_3578_);
lean_dec(v_a_3574_);
v___x_3579_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_typeIdOf_3578_, v_type_3545_);
if (lean_obj_tag(v___x_3579_) == 1)
{
lean_object* v_val_3580_; lean_object* v___x_3582_; 
lean_dec_ref(v_type_3545_);
v_val_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_val_3580_);
lean_dec_ref(v___x_3579_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v_val_3580_);
v___x_3582_ = v___x_3576_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_val_3580_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
else
{
lean_object* v___x_3584_; 
lean_dec(v___x_3579_);
lean_del_object(v___x_3576_);
lean_inc_ref(v_type_3545_);
v___x_3584_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; lean_object* v___f_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
lean_dec_ref(v___x_3584_);
lean_inc(v_a_3585_);
v___f_3586_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_3586_, 0, v_type_3545_);
lean_closure_set(v___f_3586_, 1, v_a_3585_);
v___x_3587_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3588_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3587_, v___f_3586_, v_a_3546_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3595_ == 0)
{
lean_object* v_unused_3596_; 
v_unused_3596_ = lean_ctor_get(v___x_3588_, 0);
lean_dec(v_unused_3596_);
v___x_3590_ = v___x_3588_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_dec(v___x_3588_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v_a_3585_);
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3585_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec(v_a_3585_);
v_a_3597_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3588_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3588_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
else
{
lean_dec_ref(v_type_3545_);
return v___x_3584_;
}
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec_ref(v_type_3545_);
v_a_3606_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3573_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3573_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
else
{
lean_object* v___x_3614_; lean_object* v___x_3616_; 
lean_dec_ref(v_type_3545_);
v___x_3614_ = lean_box(0);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3614_);
v___x_3616_ = v___x_3570_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec_ref(v_type_3545_);
v_a_3619_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3567_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3567_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v_type_3545_);
v_a_3628_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3557_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3557_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object* v_type_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_type_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
lean_dec(v_a_3646_);
lean_dec_ref(v_a_3645_);
lean_dec(v_a_3644_);
lean_dec_ref(v_a_3643_);
lean_dec(v_a_3642_);
lean_dec_ref(v_a_3641_);
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
lean_dec(v_a_3638_);
lean_dec(v_a_3637_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object* v_00_u03b2_3649_, lean_object* v_x_3650_, lean_object* v_x_3651_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_3650_, v_x_3651_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_3653_, lean_object* v_x_3654_, lean_object* v_x_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(v_00_u03b2_3653_, v_x_3654_, v_x_3655_);
lean_dec_ref(v_x_3655_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3657_, lean_object* v_x_3658_, size_t v_x_3659_, lean_object* v_x_3660_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_3658_, v_x_3659_, v_x_3660_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3662_, lean_object* v_x_3663_, lean_object* v_x_3664_, lean_object* v_x_3665_){
_start:
{
size_t v_x_8236__boxed_3666_; lean_object* v_res_3667_; 
v_x_8236__boxed_3666_ = lean_unbox_usize(v_x_3664_);
lean_dec(v_x_3664_);
v_res_3667_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(v_00_u03b2_3662_, v_x_3663_, v_x_8236__boxed_3666_, v_x_3665_);
lean_dec_ref(v_x_3665_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3668_, lean_object* v_keys_3669_, lean_object* v_vals_3670_, lean_object* v_heq_3671_, lean_object* v_i_3672_, lean_object* v_k_3673_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3669_, v_vals_3670_, v_i_3672_, v_k_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3675_, lean_object* v_keys_3676_, lean_object* v_vals_3677_, lean_object* v_heq_3678_, lean_object* v_i_3679_, lean_object* v_k_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_3675_, v_keys_3676_, v_vals_3677_, v_heq_3678_, v_i_3679_, v_k_3680_);
lean_dec_ref(v_k_3680_);
lean_dec_ref(v_vals_3677_);
lean_dec_ref(v_keys_3676_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object* v_u_3682_, lean_object* v_type_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3689_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_3690_ = lean_box(0);
v___x_3691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3691_, 0, v_u_3682_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
v___x_3692_ = l_Lean_mkConst(v___x_3689_, v___x_3691_);
v___x_3693_ = l_Lean_Expr_app___override(v___x_3692_, v_type_3683_);
v___x_3694_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_3693_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object* v_u_3695_, lean_object* v_type_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_3695_, v_type_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
lean_dec(v_a_3700_);
lean_dec_ref(v_a_3699_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object* v_u_3703_, lean_object* v_type_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_3703_, v_type_3704_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object* v_u_3717_, lean_object* v_type_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(v_u_3717_, v_type_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_);
lean_dec(v_a_3728_);
lean_dec_ref(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_a_3725_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
lean_dec(v_a_3720_);
lean_dec(v_a_3719_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object* v___x_3731_, lean_object* v_s_3732_){
_start:
{
lean_object* v_structs_3733_; lean_object* v_typeIdOf_3734_; lean_object* v_exprToStructId_3735_; lean_object* v_exprToStructIdEntries_3736_; lean_object* v_forbiddenNatModules_3737_; lean_object* v_natStructs_3738_; lean_object* v_natTypeIdOf_3739_; lean_object* v_exprToNatStructId_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3748_; 
v_structs_3733_ = lean_ctor_get(v_s_3732_, 0);
v_typeIdOf_3734_ = lean_ctor_get(v_s_3732_, 1);
v_exprToStructId_3735_ = lean_ctor_get(v_s_3732_, 2);
v_exprToStructIdEntries_3736_ = lean_ctor_get(v_s_3732_, 3);
v_forbiddenNatModules_3737_ = lean_ctor_get(v_s_3732_, 4);
v_natStructs_3738_ = lean_ctor_get(v_s_3732_, 5);
v_natTypeIdOf_3739_ = lean_ctor_get(v_s_3732_, 6);
v_exprToNatStructId_3740_ = lean_ctor_get(v_s_3732_, 7);
v_isSharedCheck_3748_ = !lean_is_exclusive(v_s_3732_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3742_ = v_s_3732_;
v_isShared_3743_ = v_isSharedCheck_3748_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_exprToNatStructId_3740_);
lean_inc(v_natTypeIdOf_3739_);
lean_inc(v_natStructs_3738_);
lean_inc(v_forbiddenNatModules_3737_);
lean_inc(v_exprToStructIdEntries_3736_);
lean_inc(v_exprToStructId_3735_);
lean_inc(v_typeIdOf_3734_);
lean_inc(v_structs_3733_);
lean_dec(v_s_3732_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3748_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; lean_object* v___x_3746_; 
v___x_3744_ = lean_array_push(v_natStructs_3738_, v___x_3731_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 5, v___x_3744_);
v___x_3746_ = v___x_3742_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_structs_3733_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_typeIdOf_3734_);
lean_ctor_set(v_reuseFailAlloc_3747_, 2, v_exprToStructId_3735_);
lean_ctor_set(v_reuseFailAlloc_3747_, 3, v_exprToStructIdEntries_3736_);
lean_ctor_set(v_reuseFailAlloc_3747_, 4, v_forbiddenNatModules_3737_);
lean_ctor_set(v_reuseFailAlloc_3747_, 5, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3747_, 6, v_natTypeIdOf_3739_);
lean_ctor_set(v_reuseFailAlloc_3747_, 7, v_exprToNatStructId_3740_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_ref_3755_; lean_object* v___x_3756_; lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3765_; 
v_ref_3755_ = lean_ctor_get(v___y_3752_, 5);
v___x_3756_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3765_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3765_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3761_; lean_object* v___x_3763_; 
lean_inc(v_ref_3755_);
v___x_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3761_, 0, v_ref_3755_);
lean_ctor_set(v___x_3761_, 1, v_a_3757_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set_tag(v___x_3759_, 1);
lean_ctor_set(v___x_3759_, 0, v___x_3761_);
v___x_3763_ = v___x_3759_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3761_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
return v_res_3772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12(void){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3801_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13(void){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12);
v___x_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
return v___x_3803_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15(void){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14));
v___x_3806_ = l_Lean_stringToMessageData(v___x_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object* v_type_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_){
_start:
{
lean_object* v___x_3819_; 
lean_inc_ref(v_type_3807_);
v___x_3819_ = l_Lean_Meta_getDecLevel(v_type_3807_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3821_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref(v___x_3819_);
lean_inc_ref(v_type_3807_);
lean_inc(v_a_3820_);
v___x_3821_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_a_3820_, v_type_3807_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_4114_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_3824_ = v___x_3821_;
v_isShared_3825_ = v_isSharedCheck_4114_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3821_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_4114_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
if (lean_obj_tag(v_a_3822_) == 1)
{
lean_object* v_val_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_del_object(v___x_3824_);
v_val_3826_ = lean_ctor_get(v_a_3822_, 0);
lean_inc(v_val_3826_);
lean_dec_ref(v_a_3822_);
v___x_3827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2));
v___x_3828_ = lean_box(0);
lean_inc(v_a_3820_);
v___x_3829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3829_, 0, v_a_3820_);
lean_ctor_set(v___x_3829_, 1, v___x_3828_);
lean_inc_ref(v___x_3829_);
v___x_3830_ = l_Lean_mkConst(v___x_3827_, v___x_3829_);
lean_inc(v_val_3826_);
lean_inc_ref(v_type_3807_);
v___x_3831_ = l_Lean_mkAppB(v___x_3830_, v_type_3807_, v_val_3826_);
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc(v_a_3815_);
lean_inc_ref(v_a_3814_);
lean_inc(v_a_3813_);
lean_inc_ref(v_a_3812_);
lean_inc(v_a_3811_);
lean_inc_ref(v_a_3810_);
lean_inc(v_a_3809_);
lean_inc(v_a_3808_);
v___x_3832_ = lean_grind_canon(v___x_3831_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3834_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref(v___x_3832_);
v___x_3834_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3833_, v_a_3813_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3836_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref(v___x_3834_);
lean_inc(v_a_3835_);
v___x_3836_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_a_3835_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref(v___x_3836_);
if (lean_obj_tag(v_a_3837_) == 1)
{
lean_object* v_val_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_4089_; 
v_val_3838_ = lean_ctor_get(v_a_3837_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_a_3837_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_3840_ = v_a_3837_;
v_isShared_3841_ = v_isSharedCheck_4089_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_val_3838_);
lean_dec(v_a_3837_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_4089_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
lean_inc_ref(v_type_3807_);
lean_inc(v_a_3820_);
v___x_3843_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3842_, v_a_3820_, v_type_3807_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref(v___x_3843_);
v___x_3845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3));
lean_inc_ref(v_type_3807_);
lean_inc(v_a_3820_);
v___x_3846_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3845_, v_a_3820_, v_type_3807_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3848_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref(v___x_3846_);
lean_inc(v_a_3844_);
lean_inc_ref(v_type_3807_);
lean_inc(v_a_3820_);
v___x_3848_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_a_3820_, v_type_3807_, v_a_3844_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3850_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref(v___x_3848_);
lean_inc(v_a_3844_);
lean_inc(v_a_3847_);
lean_inc_ref(v_type_3807_);
lean_inc(v_a_3820_);
v___x_3850_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_a_3820_, v_type_3807_, v_a_3847_, v_a_3844_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; lean_object* v___x_3852_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref(v___x_3850_);
lean_inc(v_a_3844_);
lean_inc_ref(v_type_3807_);
lean_inc(v_a_3820_);
v___x_3852_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_a_3820_, v_type_3807_, v_a_3844_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref(v___x_3852_);
v___x_3854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62));
lean_inc_ref(v_type_3807_);
lean_inc(v_a_3820_);
v___x_3855_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v___x_3854_, v_a_3820_, v_type_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref(v___x_3855_);
v___x_3857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64));
lean_inc_ref(v___x_3829_);
lean_inc(v_a_3820_);
v___x_3858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3858_, 0, v_a_3820_);
lean_ctor_set(v___x_3858_, 1, v___x_3829_);
lean_inc_ref(v___x_3858_);
lean_inc(v_a_3820_);
v___x_3859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3859_, 0, v_a_3820_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v___x_3860_ = l_Lean_mkConst(v___x_3857_, v___x_3859_);
lean_inc(v_a_3856_);
lean_inc_ref_n(v_type_3807_, 3);
v___x_3861_ = l_Lean_mkApp4(v___x_3860_, v_type_3807_, v_type_3807_, v_type_3807_, v_a_3856_);
v___x_3862_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_3861_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; lean_object* v_orderedAddInst_x3f_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref(v___x_3862_);
if (lean_obj_tag(v_a_3844_) == 1)
{
if (lean_obj_tag(v_a_3849_) == 1)
{
lean_object* v_val_4018_; lean_object* v_val_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v_val_4018_ = lean_ctor_get(v_a_3844_, 0);
v_val_4019_ = lean_ctor_get(v_a_3849_, 0);
v___x_4020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66));
lean_inc_ref(v___x_3829_);
v___x_4021_ = l_Lean_mkConst(v___x_4020_, v___x_3829_);
lean_inc(v_val_4019_);
lean_inc(v_val_4018_);
lean_inc_ref(v_type_3807_);
v___x_4022_ = l_Lean_mkApp4(v___x_4021_, v_type_3807_, v_a_3856_, v_val_4018_, v_val_4019_);
v___x_4023_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_4022_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref(v___x_4023_);
v_orderedAddInst_x3f_3865_ = v_a_4024_;
v___y_3866_ = v_a_3808_;
v___y_3867_ = v_a_3809_;
v___y_3868_ = v_a_3810_;
v___y_3869_ = v_a_3811_;
v___y_3870_ = v_a_3812_;
v___y_3871_ = v_a_3813_;
v___y_3872_ = v_a_3814_;
v___y_3873_ = v_a_3815_;
v___y_3874_ = v_a_3816_;
v___y_3875_ = v_a_3817_;
goto v___jp_3864_;
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec_ref(v_a_3849_);
lean_dec_ref(v_a_3844_);
lean_dec(v_a_3863_);
lean_dec_ref(v___x_3858_);
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec(v_a_3847_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_4025_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_4023_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4023_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
else
{
lean_dec(v_a_3856_);
v___y_4007_ = v_a_3808_;
v___y_4008_ = v_a_3809_;
v___y_4009_ = v_a_3810_;
v___y_4010_ = v_a_3811_;
v___y_4011_ = v_a_3812_;
v___y_4012_ = v_a_3813_;
v___y_4013_ = v_a_3814_;
v___y_4014_ = v_a_3815_;
v___y_4015_ = v_a_3816_;
v___y_4016_ = v_a_3817_;
goto v___jp_4006_;
}
}
else
{
lean_dec(v_a_3856_);
v___y_4007_ = v_a_3808_;
v___y_4008_ = v_a_3809_;
v___y_4009_ = v_a_3810_;
v___y_4010_ = v_a_3811_;
v___y_4011_ = v_a_3812_;
v___y_4012_ = v_a_3813_;
v___y_4013_ = v_a_3814_;
v___y_4014_ = v_a_3815_;
v___y_4015_ = v_a_3816_;
v___y_4016_ = v_a_3817_;
goto v___jp_4006_;
}
v___jp_3864_:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4));
lean_inc_ref(v___x_3829_);
v___x_3877_ = l_Lean_mkConst(v___x_3876_, v___x_3829_);
lean_inc_ref(v_type_3807_);
v___x_3878_ = l_Lean_Expr_app___override(v___x_3877_, v_type_3807_);
v___x_3879_ = l_Lean_Meta_Grind_synthInstance(v___x_3878_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref(v___x_3879_);
v___x_3881_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6));
lean_inc_ref(v___x_3829_);
v___x_3882_ = l_Lean_mkConst(v___x_3881_, v___x_3829_);
lean_inc_ref(v_type_3807_);
v___x_3883_ = l_Lean_mkAppB(v___x_3882_, v_type_3807_, v_a_3880_);
v___x_3884_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_3883_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref(v___x_3884_);
v___x_3886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8));
lean_inc_ref(v___x_3829_);
v___x_3887_ = l_Lean_mkConst(v___x_3886_, v___x_3829_);
lean_inc(v_val_3826_);
lean_inc_ref(v_type_3807_);
v___x_3888_ = l_Lean_mkAppB(v___x_3887_, v_type_3807_, v_val_3826_);
v___x_3889_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_3888_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref(v___x_3889_);
v___x_3891_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14));
lean_inc_ref(v_type_3807_);
lean_inc(v_a_3820_);
v___x_3892_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v___x_3891_, v_a_3820_, v_type_3807_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref(v___x_3892_);
v___x_3894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16));
v___x_3895_ = l_Lean_mkConst(v___x_3894_, v___x_3829_);
lean_inc_ref(v_type_3807_);
v___x_3896_ = l_Lean_mkAppB(v___x_3895_, v_type_3807_, v_a_3893_);
v___x_3897_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_3896_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3899_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref(v___x_3897_);
lean_inc_ref(v_type_3807_);
lean_inc(v_a_3820_);
v___x_3899_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_a_3820_, v_type_3807_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref(v___x_3899_);
v___x_3901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___closed__1));
v___x_3902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___closed__2);
v___x_3903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v___x_3858_);
v___x_3904_ = l_Lean_mkConst(v___x_3901_, v___x_3903_);
v___x_3905_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_3807_, 2);
v___x_3906_ = l_Lean_mkApp4(v___x_3904_, v___x_3905_, v_type_3807_, v_type_3807_, v_a_3900_);
v___x_3907_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v___x_3906_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref(v___x_3907_);
v___x_3909_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_3866_, v___y_3874_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v_natStructs_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___f_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref(v___x_3909_);
v_natStructs_3911_ = lean_ctor_get(v_a_3910_, 5);
lean_inc_ref(v_natStructs_3911_);
lean_dec(v_a_3910_);
v___x_3912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11));
lean_inc(v_a_3820_);
v___x_3913_ = l_Lean_Level_succ___override(v_a_3820_);
v___x_3914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
lean_ctor_set(v___x_3914_, 1, v___x_3828_);
v___x_3915_ = l_Lean_mkConst(v___x_3912_, v___x_3914_);
v___x_3916_ = l_Lean_Expr_app___override(v___x_3915_, v_a_3835_);
v___x_3917_ = lean_array_get_size(v_natStructs_3911_);
lean_dec_ref(v_natStructs_3911_);
v___x_3918_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13);
v___x_3919_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3917_);
lean_ctor_set(v___x_3919_, 1, v_val_3838_);
lean_ctor_set(v___x_3919_, 2, v_type_3807_);
lean_ctor_set(v___x_3919_, 3, v_a_3820_);
lean_ctor_set(v___x_3919_, 4, v_val_3826_);
lean_ctor_set(v___x_3919_, 5, v_a_3844_);
lean_ctor_set(v___x_3919_, 6, v_a_3847_);
lean_ctor_set(v___x_3919_, 7, v_a_3851_);
lean_ctor_set(v___x_3919_, 8, v_a_3849_);
lean_ctor_set(v___x_3919_, 9, v_orderedAddInst_x3f_3865_);
lean_ctor_set(v___x_3919_, 10, v_a_3853_);
lean_ctor_set(v___x_3919_, 11, v_a_3885_);
lean_ctor_set(v___x_3919_, 12, v___x_3916_);
lean_ctor_set(v___x_3919_, 13, v_a_3898_);
lean_ctor_set(v___x_3919_, 14, v_a_3890_);
lean_ctor_set(v___x_3919_, 15, v_a_3863_);
lean_ctor_set(v___x_3919_, 16, v_a_3908_);
lean_ctor_set(v___x_3919_, 17, v___x_3918_);
v___f_3920_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_3920_, 0, v___x_3919_);
v___x_3921_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3922_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3921_, v___f_3920_, v___y_3866_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3932_; 
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3932_ == 0)
{
lean_object* v_unused_3933_; 
v_unused_3933_ = lean_ctor_get(v___x_3922_, 0);
lean_dec(v_unused_3933_);
v___x_3924_ = v___x_3922_;
v_isShared_3925_ = v_isSharedCheck_3932_;
goto v_resetjp_3923_;
}
else
{
lean_dec(v___x_3922_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3932_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v___x_3917_);
v___x_3927_ = v___x_3840_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3917_);
v___x_3927_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3929_; 
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 0, v___x_3927_);
v___x_3929_ = v___x_3924_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_del_object(v___x_3840_);
v_a_3934_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3922_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3922_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_dec(v_a_3908_);
lean_dec(v_a_3898_);
lean_dec(v_a_3890_);
lean_dec(v_a_3885_);
lean_dec(v_orderedAddInst_x3f_3865_);
lean_dec(v_a_3863_);
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_3942_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3909_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3909_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
else
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3957_; 
lean_dec(v_a_3898_);
lean_dec(v_a_3890_);
lean_dec(v_a_3885_);
lean_dec(v_orderedAddInst_x3f_3865_);
lean_dec(v_a_3863_);
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_3950_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3952_ = v___x_3907_;
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3907_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec(v_a_3898_);
lean_dec(v_a_3890_);
lean_dec(v_a_3885_);
lean_dec(v_orderedAddInst_x3f_3865_);
lean_dec(v_a_3863_);
lean_dec_ref(v___x_3858_);
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_3958_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3899_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3899_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v_a_3890_);
lean_dec(v_a_3885_);
lean_dec(v_orderedAddInst_x3f_3865_);
lean_dec(v_a_3863_);
lean_dec_ref(v___x_3858_);
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_3966_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3897_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3897_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
lean_dec(v_a_3890_);
lean_dec(v_a_3885_);
lean_dec(v_orderedAddInst_x3f_3865_);
lean_dec(v_a_3863_);
lean_dec_ref(v___x_3858_);
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_3974_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3892_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3892_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec(v_a_3885_);
lean_dec(v_orderedAddInst_x3f_3865_);
lean_dec(v_a_3863_);
lean_dec_ref(v___x_3858_);
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_3982_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3889_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3889_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v_orderedAddInst_x3f_3865_);
lean_dec(v_a_3863_);
lean_dec_ref(v___x_3858_);
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_3990_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3884_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3884_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_dec(v_orderedAddInst_x3f_3865_);
lean_dec(v_a_3863_);
lean_dec_ref(v___x_3858_);
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_3998_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3879_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3879_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
v___jp_4006_:
{
lean_object* v___x_4017_; 
v___x_4017_ = lean_box(0);
v_orderedAddInst_x3f_3865_ = v___x_4017_;
v___y_3866_ = v___y_4007_;
v___y_3867_ = v___y_4008_;
v___y_3868_ = v___y_4009_;
v___y_3869_ = v___y_4010_;
v___y_3870_ = v___y_4011_;
v___y_3871_ = v___y_4012_;
v___y_3872_ = v___y_4013_;
v___y_3873_ = v___y_4014_;
v___y_3874_ = v___y_4015_;
v___y_3875_ = v___y_4016_;
goto v___jp_3864_;
}
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec_ref(v___x_3858_);
lean_dec(v_a_3856_);
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_4033_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_3862_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_3862_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_4041_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_3855_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_3855_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec(v_a_3851_);
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_4049_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_3852_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_3852_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec(v_a_3849_);
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_4057_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_3850_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_3850_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec(v_a_3847_);
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_4065_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_3848_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_3848_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v_a_3844_);
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_4073_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_3846_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_3846_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_del_object(v___x_3840_);
lean_dec(v_val_3838_);
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_4081_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_3843_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_3843_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
}
else
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
lean_dec(v_a_3837_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v___x_4090_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15);
v___x_4091_ = l_Lean_indentExpr(v_a_3835_);
v___x_4092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v___x_4092_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
return v___x_4093_;
}
}
else
{
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
return v___x_3836_;
}
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_4094_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_3834_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_3834_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
else
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4109_; 
lean_dec_ref(v___x_3829_);
lean_dec(v_val_3826_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_4102_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4104_ = v___x_3832_;
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_3832_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4107_; 
if (v_isShared_4105_ == 0)
{
v___x_4107_ = v___x_4104_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_4102_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
}
else
{
lean_object* v___x_4110_; lean_object* v___x_4112_; 
lean_dec(v_a_3822_);
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v___x_4110_ = lean_box(0);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_4110_);
v___x_4112_ = v___x_3824_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4110_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_dec(v_a_3820_);
lean_dec_ref(v_type_3807_);
v_a_4115_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_3821_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_3821_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec_ref(v_type_3807_);
v_a_4123_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_3819_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_3819_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object* v_type_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
lean_dec(v_a_4139_);
lean_dec_ref(v_a_4138_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
lean_dec(v_a_4133_);
lean_dec(v_a_4132_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_4144_, lean_object* v_msg_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v___x_4157_; 
v___x_4157_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_4145_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_4158_, lean_object* v_msg_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(v_00_u03b1_4158_, v_msg_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec(v___y_4160_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object* v_type_4172_, lean_object* v_a_4173_, lean_object* v_s_4174_){
_start:
{
lean_object* v_structs_4175_; lean_object* v_typeIdOf_4176_; lean_object* v_exprToStructId_4177_; lean_object* v_exprToStructIdEntries_4178_; lean_object* v_forbiddenNatModules_4179_; lean_object* v_natStructs_4180_; lean_object* v_natTypeIdOf_4181_; lean_object* v_exprToNatStructId_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4190_; 
v_structs_4175_ = lean_ctor_get(v_s_4174_, 0);
v_typeIdOf_4176_ = lean_ctor_get(v_s_4174_, 1);
v_exprToStructId_4177_ = lean_ctor_get(v_s_4174_, 2);
v_exprToStructIdEntries_4178_ = lean_ctor_get(v_s_4174_, 3);
v_forbiddenNatModules_4179_ = lean_ctor_get(v_s_4174_, 4);
v_natStructs_4180_ = lean_ctor_get(v_s_4174_, 5);
v_natTypeIdOf_4181_ = lean_ctor_get(v_s_4174_, 6);
v_exprToNatStructId_4182_ = lean_ctor_get(v_s_4174_, 7);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_s_4174_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4184_ = v_s_4174_;
v_isShared_4185_ = v_isSharedCheck_4190_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_exprToNatStructId_4182_);
lean_inc(v_natTypeIdOf_4181_);
lean_inc(v_natStructs_4180_);
lean_inc(v_forbiddenNatModules_4179_);
lean_inc(v_exprToStructIdEntries_4178_);
lean_inc(v_exprToStructId_4177_);
lean_inc(v_typeIdOf_4176_);
lean_inc(v_structs_4175_);
lean_dec(v_s_4174_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4190_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4186_; lean_object* v___x_4188_; 
v___x_4186_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(v_natTypeIdOf_4181_, v_type_4172_, v_a_4173_);
if (v_isShared_4185_ == 0)
{
lean_ctor_set(v___x_4184_, 6, v___x_4186_);
v___x_4188_ = v___x_4184_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_structs_4175_);
lean_ctor_set(v_reuseFailAlloc_4189_, 1, v_typeIdOf_4176_);
lean_ctor_set(v_reuseFailAlloc_4189_, 2, v_exprToStructId_4177_);
lean_ctor_set(v_reuseFailAlloc_4189_, 3, v_exprToStructIdEntries_4178_);
lean_ctor_set(v_reuseFailAlloc_4189_, 4, v_forbiddenNatModules_4179_);
lean_ctor_set(v_reuseFailAlloc_4189_, 5, v_natStructs_4180_);
lean_ctor_set(v_reuseFailAlloc_4189_, 6, v___x_4186_);
lean_ctor_set(v_reuseFailAlloc_4189_, 7, v_exprToNatStructId_4182_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4191_, lean_object* v_i_4192_, lean_object* v_k_4193_){
_start:
{
lean_object* v___x_4194_; uint8_t v___x_4195_; 
v___x_4194_ = lean_array_get_size(v_keys_4191_);
v___x_4195_ = lean_nat_dec_lt(v_i_4192_, v___x_4194_);
if (v___x_4195_ == 0)
{
lean_dec(v_i_4192_);
return v___x_4195_;
}
else
{
lean_object* v_k_x27_4196_; uint8_t v___x_4197_; 
v_k_x27_4196_ = lean_array_fget_borrowed(v_keys_4191_, v_i_4192_);
v___x_4197_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_4193_, v_k_x27_4196_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = lean_unsigned_to_nat(1u);
v___x_4199_ = lean_nat_add(v_i_4192_, v___x_4198_);
lean_dec(v_i_4192_);
v_i_4192_ = v___x_4199_;
goto _start;
}
else
{
lean_dec(v_i_4192_);
return v___x_4197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4201_, lean_object* v_i_4202_, lean_object* v_k_4203_){
_start:
{
uint8_t v_res_4204_; lean_object* v_r_4205_; 
v_res_4204_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4201_, v_i_4202_, v_k_4203_);
lean_dec_ref(v_k_4203_);
lean_dec_ref(v_keys_4201_);
v_r_4205_ = lean_box(v_res_4204_);
return v_r_4205_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_4206_, size_t v_x_4207_, lean_object* v_x_4208_){
_start:
{
if (lean_obj_tag(v_x_4206_) == 0)
{
lean_object* v_es_4209_; lean_object* v___x_4210_; size_t v___x_4211_; size_t v___x_4212_; size_t v___x_4213_; lean_object* v_j_4214_; lean_object* v___x_4215_; 
v_es_4209_ = lean_ctor_get(v_x_4206_, 0);
v___x_4210_ = lean_box(2);
v___x_4211_ = ((size_t)5ULL);
v___x_4212_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1);
v___x_4213_ = lean_usize_land(v_x_4207_, v___x_4212_);
v_j_4214_ = lean_usize_to_nat(v___x_4213_);
v___x_4215_ = lean_array_get_borrowed(v___x_4210_, v_es_4209_, v_j_4214_);
lean_dec(v_j_4214_);
switch(lean_obj_tag(v___x_4215_))
{
case 0:
{
lean_object* v_key_4216_; uint8_t v___x_4217_; 
v_key_4216_ = lean_ctor_get(v___x_4215_, 0);
v___x_4217_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_4208_, v_key_4216_);
return v___x_4217_;
}
case 1:
{
lean_object* v_node_4218_; size_t v___x_4219_; 
v_node_4218_ = lean_ctor_get(v___x_4215_, 0);
v___x_4219_ = lean_usize_shift_right(v_x_4207_, v___x_4211_);
v_x_4206_ = v_node_4218_;
v_x_4207_ = v___x_4219_;
goto _start;
}
default: 
{
uint8_t v___x_4221_; 
v___x_4221_ = 0;
return v___x_4221_;
}
}
}
else
{
lean_object* v_ks_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; 
v_ks_4222_ = lean_ctor_get(v_x_4206_, 0);
v___x_4223_ = lean_unsigned_to_nat(0u);
v___x_4224_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4222_, v___x_4223_, v_x_4208_);
return v___x_4224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4225_, lean_object* v_x_4226_, lean_object* v_x_4227_){
_start:
{
size_t v_x_10574__boxed_4228_; uint8_t v_res_4229_; lean_object* v_r_4230_; 
v_x_10574__boxed_4228_ = lean_unbox_usize(v_x_4226_);
lean_dec(v_x_4226_);
v_res_4229_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_4225_, v_x_10574__boxed_4228_, v_x_4227_);
lean_dec_ref(v_x_4227_);
lean_dec_ref(v_x_4225_);
v_r_4230_ = lean_box(v_res_4229_);
return v_r_4230_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object* v_x_4231_, lean_object* v_x_4232_){
_start:
{
uint64_t v___x_4233_; size_t v___x_4234_; uint8_t v___x_4235_; 
v___x_4233_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_4232_);
v___x_4234_ = lean_uint64_to_usize(v___x_4233_);
v___x_4235_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_4231_, v___x_4234_, v_x_4232_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_4236_, lean_object* v_x_4237_){
_start:
{
uint8_t v_res_4238_; lean_object* v_r_4239_; 
v_res_4238_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_4236_, v_x_4237_);
lean_dec_ref(v_x_4237_);
lean_dec_ref(v_x_4236_);
v_r_4239_ = lean_box(v_res_4238_);
return v_r_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object* v_type_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4243_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4342_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4255_ = v___x_4252_;
v_isShared_4256_ = v_isSharedCheck_4342_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4342_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
uint8_t v_linarith_4257_; 
v_linarith_4257_ = lean_ctor_get_uint8(v_a_4253_, sizeof(void*)*11 + 22);
lean_dec(v_a_4253_);
if (v_linarith_4257_ == 0)
{
lean_object* v___x_4258_; lean_object* v___x_4260_; 
lean_dec_ref(v_type_4240_);
v___x_4258_ = lean_box(0);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v___x_4258_);
v___x_4260_ = v___x_4255_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4258_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
else
{
lean_object* v___x_4262_; 
lean_del_object(v___x_4255_);
v___x_4262_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_4241_, v_a_4249_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4333_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4265_ = v___x_4262_;
v_isShared_4266_ = v_isSharedCheck_4333_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4262_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4333_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v_forbiddenNatModules_4267_; uint8_t v___x_4268_; 
v_forbiddenNatModules_4267_ = lean_ctor_get(v_a_4263_, 4);
lean_inc_ref(v_forbiddenNatModules_4267_);
lean_dec(v_a_4263_);
v___x_4268_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_forbiddenNatModules_4267_, v_type_4240_);
lean_dec_ref(v_forbiddenNatModules_4267_);
if (v___x_4268_ == 0)
{
lean_object* v___x_4269_; 
lean_del_object(v___x_4265_);
lean_inc_ref(v_type_4240_);
v___x_4269_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4320_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4320_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4320_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
uint8_t v___x_4274_; 
v___x_4274_ = lean_unbox(v_a_4270_);
lean_dec(v_a_4270_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; 
lean_del_object(v___x_4272_);
v___x_4275_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_4241_, v_a_4249_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4307_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4278_ = v___x_4275_;
v_isShared_4279_ = v_isSharedCheck_4307_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4307_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v_natTypeIdOf_4280_; lean_object* v___x_4281_; 
v_natTypeIdOf_4280_ = lean_ctor_get(v_a_4276_, 6);
lean_inc_ref(v_natTypeIdOf_4280_);
lean_dec(v_a_4276_);
v___x_4281_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_natTypeIdOf_4280_, v_type_4240_);
if (lean_obj_tag(v___x_4281_) == 1)
{
lean_object* v_val_4282_; lean_object* v___x_4284_; 
lean_dec_ref(v_type_4240_);
v_val_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_val_4282_);
lean_dec_ref(v___x_4281_);
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 0, v_val_4282_);
v___x_4284_ = v___x_4278_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_val_4282_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
else
{
lean_object* v___x_4286_; 
lean_dec(v___x_4281_);
lean_del_object(v___x_4278_);
lean_inc_ref(v_type_4240_);
v___x_4286_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_);
if (lean_obj_tag(v___x_4286_) == 0)
{
lean_object* v_a_4287_; lean_object* v___f_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v_a_4287_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_a_4287_);
lean_dec_ref(v___x_4286_);
lean_inc(v_a_4287_);
v___f_4288_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_4288_, 0, v_type_4240_);
lean_closure_set(v___f_4288_, 1, v_a_4287_);
v___x_4289_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4290_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4289_, v___f_4288_, v_a_4241_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4297_ == 0)
{
lean_object* v_unused_4298_; 
v_unused_4298_ = lean_ctor_get(v___x_4290_, 0);
lean_dec(v_unused_4298_);
v___x_4292_ = v___x_4290_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_dec(v___x_4290_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v_a_4287_);
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4287_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
lean_dec(v_a_4287_);
v_a_4299_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4290_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4290_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
else
{
lean_dec_ref(v_type_4240_);
return v___x_4286_;
}
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref(v_type_4240_);
v_a_4308_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4275_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4275_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
else
{
lean_object* v___x_4316_; lean_object* v___x_4318_; 
lean_dec_ref(v_type_4240_);
v___x_4316_ = lean_box(0);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v___x_4316_);
v___x_4318_ = v___x_4272_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4316_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_dec_ref(v_type_4240_);
v_a_4321_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4269_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4269_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
else
{
lean_object* v___x_4329_; lean_object* v___x_4331_; 
lean_dec_ref(v_type_4240_);
v___x_4329_ = lean_box(0);
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 0, v___x_4329_);
v___x_4331_ = v___x_4265_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec_ref(v_type_4240_);
v_a_4334_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4262_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4262_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec_ref(v_type_4240_);
v_a_4343_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4252_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4252_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object* v_type_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_type_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
lean_dec(v_a_4359_);
lean_dec_ref(v_a_4358_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
lean_dec(v_a_4353_);
lean_dec(v_a_4352_);
return v_res_4363_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object* v_00_u03b2_4364_, lean_object* v_x_4365_, lean_object* v_x_4366_){
_start:
{
uint8_t v___x_4367_; 
v___x_4367_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_4365_, v_x_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_4368_, lean_object* v_x_4369_, lean_object* v_x_4370_){
_start:
{
uint8_t v_res_4371_; lean_object* v_r_4372_; 
v_res_4371_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(v_00_u03b2_4368_, v_x_4369_, v_x_4370_);
lean_dec_ref(v_x_4370_);
lean_dec_ref(v_x_4369_);
v_r_4372_ = lean_box(v_res_4371_);
return v_r_4372_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4373_, lean_object* v_x_4374_, size_t v_x_4375_, lean_object* v_x_4376_){
_start:
{
uint8_t v___x_4377_; 
v___x_4377_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_4374_, v_x_4375_, v_x_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4378_, lean_object* v_x_4379_, lean_object* v_x_4380_, lean_object* v_x_4381_){
_start:
{
size_t v_x_10834__boxed_4382_; uint8_t v_res_4383_; lean_object* v_r_4384_; 
v_x_10834__boxed_4382_ = lean_unbox_usize(v_x_4380_);
lean_dec(v_x_4380_);
v_res_4383_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(v_00_u03b2_4378_, v_x_4379_, v_x_10834__boxed_4382_, v_x_4381_);
lean_dec_ref(v_x_4381_);
lean_dec_ref(v_x_4379_);
v_r_4384_ = lean_box(v_res_4383_);
return v_r_4384_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4385_, lean_object* v_keys_4386_, lean_object* v_vals_4387_, lean_object* v_heq_4388_, lean_object* v_i_4389_, lean_object* v_k_4390_){
_start:
{
uint8_t v___x_4391_; 
v___x_4391_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4386_, v_i_4389_, v_k_4390_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4392_, lean_object* v_keys_4393_, lean_object* v_vals_4394_, lean_object* v_heq_4395_, lean_object* v_i_4396_, lean_object* v_k_4397_){
_start:
{
uint8_t v_res_4398_; lean_object* v_r_4399_; 
v_res_4398_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4392_, v_keys_4393_, v_vals_4394_, v_heq_4395_, v_i_4396_, v_k_4397_);
lean_dec_ref(v_k_4397_);
lean_dec_ref(v_vals_4394_);
lean_dec_ref(v_keys_4393_);
v_r_4399_ = lean_box(v_res_4398_);
return v_r_4399_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
}
#ifdef __cplusplus
}
#endif
