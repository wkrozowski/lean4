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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0_value;
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1_value;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = l_Lean_instBEqFVarId_beq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc_ref(x_3);
lean_inc(x_7);
x_10 = l_Lean_FVarId_getDecl___redArg(x_7, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_8);
x_12 = l_Lean_FVarId_getDecl___redArg(x_8, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_26; 
x_13 = lean_ctor_get(x_12, 0);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
x_14 = x_12;
x_15 = x_26;
goto block_25;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_LocalDecl_index(x_13);
lean_dec(x_13);
x_17 = l_Lean_LocalDecl_index(x_11);
lean_dec(x_11);
x_18 = lean_nat_dec_lt(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_1);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_2);
x_19 = x_14;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_2);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; 
lean_dec_ref(x_2);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_1);
x_22 = x_14;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_11);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_12, 0);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
x_28 = x_12;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_12);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_dec_ref(x_3);
x_35 = lean_ctor_get(x_10, 0);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
x_36 = x_10;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec_ref(x_3);
x_49 = !lean_is_exclusive(x_2);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_2, 0);
lean_dec(x_50);
x_43 = x_2;
x_44 = x_49;
goto block_48;
}
else
{
lean_dec(x_2);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
lean_ctor_set_tag(x_43, 0);
lean_ctor_set(x_43, 0, x_1);
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_1);
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
lean_object* x_51; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_1);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_2);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(x_1, x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; uint8_t x_54; 
x_54 = l_Lean_Expr_hasFVar(x_1);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = l_Lean_Expr_hasMVar(x_1);
x_10 = x_55;
goto block_53;
}
else
{
x_10 = x_54;
goto block_53;
}
block_53:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_st_ref_get(x_4);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__0));
x_16 = ((lean_object*)(l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___closed__1));
lean_inc_ref(x_1);
x_17 = l_Lean_PersistentHashMap_find_x3f___redArg(x_15, x_16, x_14, x_1);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_17, 0);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
x_19 = x_17;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
lean_ctor_set_tag(x_19, 0);
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* x_26; 
lean_dec(x_17);
lean_inc(x_4);
x_26 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_52; 
x_27 = lean_ctor_get(x_26, 0);
x_52 = !lean_is_exclusive(x_26);
if (x_52 == 0)
{
x_28 = x_26;
x_29 = x_52;
goto block_51;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; uint8_t x_50; 
x_30 = lean_st_ref_take(x_4);
x_31 = lean_ctor_get(x_30, 0);
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 2);
x_34 = lean_ctor_get(x_30, 3);
x_35 = lean_ctor_get(x_30, 4);
x_36 = lean_ctor_get(x_30, 5);
x_37 = lean_ctor_get(x_30, 6);
x_38 = lean_ctor_get_uint8(x_30, sizeof(void*)*7);
x_50 = !lean_is_exclusive(x_30);
if (x_50 == 0)
{
x_39 = x_30;
x_40 = x_50;
goto block_49;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_30);
x_39 = lean_box(0);
x_40 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_41; lean_object* x_42; 
lean_inc(x_27);
x_41 = l_Lean_PersistentHashMap_insert___redArg(x_15, x_16, x_32, x_1, x_27);
if (x_40 == 0)
{
lean_ctor_set(x_39, 1, x_41);
x_42 = x_39;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_48, 0, x_31);
lean_ctor_set(x_48, 1, x_41);
lean_ctor_set(x_48, 2, x_33);
lean_ctor_set(x_48, 3, x_34);
lean_ctor_set(x_48, 4, x_35);
lean_ctor_set(x_48, 5, x_36);
lean_ctor_set(x_48, 6, x_37);
lean_ctor_set_uint8(x_48, sizeof(void*)*7, x_38);
x_42 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_st_ref_set(x_4, x_42);
lean_dec(x_4);
if (x_29 == 0)
{
x_44 = x_28;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_27);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_check(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_74; 
x_9 = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__0);
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
x_74 = !lean_is_exclusive(x_10);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_10, 1);
lean_dec(x_75);
x_12 = x_10;
x_13 = x_74;
goto block_73;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_71; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_71 = !lean_is_exclusive(x_11);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_11, 1);
lean_dec(x_72);
x_18 = x_11;
x_19 = x_71;
goto block_70;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__1));
x_21 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__2));
lean_inc_ref(x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_16);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_15);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_25);
lean_ctor_set(x_18, 3, x_26);
lean_ctor_set(x_18, 2, x_27);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_24);
x_28 = x_18;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_24);
lean_ctor_set(x_69, 1, x_20);
lean_ctor_set(x_69, 2, x_27);
lean_ctor_set(x_69, 3, x_26);
lean_ctor_set(x_69, 4, x_25);
x_28 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_29; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_28);
x_29 = x_12;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_28);
lean_ctor_set(x_67, 1, x_21);
x_29 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_64; 
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = lean_ctor_get(x_30, 0);
x_64 = !lean_is_exclusive(x_30);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_30, 1);
lean_dec(x_65);
x_32 = x_30;
x_33 = x_64;
goto block_63;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_61; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_61 = !lean_is_exclusive(x_31);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_31, 1);
lean_dec(x_62);
x_38 = x_31;
x_39 = x_61;
goto block_60;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__3));
x_41 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___closed__4));
lean_inc_ref(x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_36);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_47, 0, x_35);
if (x_39 == 0)
{
lean_ctor_set(x_38, 4, x_45);
lean_ctor_set(x_38, 3, x_46);
lean_ctor_set(x_38, 2, x_47);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_44);
x_48 = x_38;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_40);
lean_ctor_set(x_59, 2, x_47);
lean_ctor_set(x_59, 3, x_46);
lean_ctor_set(x_59, 4, x_45);
x_48 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_49; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 1, x_41);
lean_ctor_set(x_32, 0, x_48);
x_49 = x_32;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_41);
x_49 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = lean_box(0);
x_52 = l_instInhabitedOfMonad___redArg(x_50, x_51);
x_53 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_panic_fn(x_53, x_1);
x_55 = lean_apply_7(x_54, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_55;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
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
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__2);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_4 = lean_ctor_get(x_1, 0);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
x_5 = x_1;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(2);
x_8 = 5;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get(x_7, x_4, x_11);
lean_dec(x_11);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_del_object(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
x_17 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_del_object(x_5);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_del_object(x_5);
x_23 = lean_box(0);
return x_23;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(x_26, x_27, x_28, x_3);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__2));
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_unsigned_to_nat(52u);
x_4 = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__1));
x_5 = ((lean_object*)(l_Lean_Meta_Sym_getMaxFVar_x3f___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_37; lean_object* x_38; lean_object* x_59; lean_object* x_60; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_129; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
lean_dec_ref(x_1);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
case 2:
{
lean_object* x_160; uint8_t x_161; uint8_t x_203; 
x_160 = lean_ctor_get(x_1, 0);
x_203 = l_Lean_Expr_hasFVar(x_1);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = l_Lean_Expr_hasMVar(x_1);
x_161 = x_204;
goto block_202;
}
else
{
x_161 = x_203;
goto block_202;
}
block_202:
{
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_st_ref_get(x_3);
x_165 = lean_ctor_get(x_164, 1);
lean_inc_ref(x_165);
lean_dec(x_164);
x_166 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(x_165, x_1);
if (lean_obj_tag(x_166) == 1)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_174; 
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_167 = lean_ctor_get(x_166, 0);
x_174 = !lean_is_exclusive(x_166);
if (x_174 == 0)
{
x_168 = x_166;
x_169 = x_174;
goto block_173;
}
else
{
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_box(0);
x_169 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_170; 
if (x_169 == 0)
{
lean_ctor_set_tag(x_168, 0);
x_170 = x_168;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_167);
x_170 = x_172;
goto block_171;
}
block_171:
{
return x_170;
}
}
}
else
{
lean_object* x_175; 
lean_dec(x_166);
lean_inc(x_160);
x_175 = l_Lean_MVarId_getDecl(x_160, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = lean_ctor_get(x_176, 1);
lean_inc_ref(x_177);
lean_dec(x_176);
x_178 = lean_ctor_get(x_177, 1);
x_179 = l_Lean_PersistentArray_isEmpty___redArg(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = l_Lean_LocalContext_lastDecl(x_177);
if (lean_obj_tag(x_180) == 1)
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; uint8_t x_189; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_181 = lean_ctor_get(x_180, 0);
x_189 = !lean_is_exclusive(x_180);
if (x_189 == 0)
{
x_182 = x_180;
x_183 = x_189;
goto block_188;
}
else
{
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_box(0);
x_183 = x_189;
goto block_188;
}
block_188:
{
lean_object* x_184; lean_object* x_185; 
x_184 = l_Lean_LocalDecl_fvarId(x_181);
lean_dec(x_181);
if (x_183 == 0)
{
lean_ctor_set(x_182, 0, x_184);
x_185 = x_182;
goto block_186;
}
else
{
lean_object* x_187; 
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_184);
x_185 = x_187;
goto block_186;
}
block_186:
{
x_37 = x_185;
x_38 = lean_box(0);
goto block_58;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_180);
x_190 = lean_obj_once(&l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3, &l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3_once, _init_l_Lean_Meta_Sym_getMaxFVar_x3f___closed__3);
lean_inc(x_3);
x_191 = l_panic___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__2(x_190, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
x_37 = x_192;
x_38 = lean_box(0);
goto block_58;
}
else
{
lean_dec_ref(x_1);
lean_dec(x_3);
return x_191;
}
}
}
else
{
lean_object* x_193; 
lean_dec_ref(x_177);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_193 = lean_box(0);
x_37 = x_193;
x_38 = lean_box(0);
goto block_58;
}
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_201; 
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_194 = lean_ctor_get(x_175, 0);
x_201 = !lean_is_exclusive(x_175);
if (x_201 == 0)
{
x_195 = x_175;
x_196 = x_201;
goto block_200;
}
else
{
lean_inc(x_194);
lean_dec(x_175);
x_195 = lean_box(0);
x_196 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_197; 
if (x_196 == 0)
{
x_197 = x_195;
goto block_198;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_194);
x_197 = x_199;
goto block_198;
}
block_198:
{
return x_197;
}
}
}
}
}
}
}
case 5:
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; uint8_t x_227; 
x_205 = lean_ctor_get(x_1, 0);
x_206 = lean_ctor_get(x_1, 1);
x_227 = l_Lean_Expr_hasFVar(x_1);
if (x_227 == 0)
{
uint8_t x_228; 
x_228 = l_Lean_Expr_hasMVar(x_1);
x_207 = x_228;
goto block_226;
}
else
{
x_207 = x_227;
goto block_226;
}
block_226:
{
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_st_ref_get(x_3);
x_211 = lean_ctor_get(x_210, 1);
lean_inc_ref(x_211);
lean_dec(x_210);
x_212 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(x_211, x_1);
if (lean_obj_tag(x_212) == 1)
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_220; 
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_213 = lean_ctor_get(x_212, 0);
x_220 = !lean_is_exclusive(x_212);
if (x_220 == 0)
{
x_214 = x_212;
x_215 = x_220;
goto block_219;
}
else
{
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_box(0);
x_215 = x_220;
goto block_219;
}
block_219:
{
lean_object* x_216; 
if (x_215 == 0)
{
lean_ctor_set_tag(x_214, 0);
x_216 = x_214;
goto block_217;
}
else
{
lean_object* x_218; 
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_213);
x_216 = x_218;
goto block_217;
}
block_217:
{
return x_216;
}
}
}
else
{
lean_object* x_221; 
lean_dec(x_212);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_205);
x_221 = l_Lean_Meta_Sym_getMaxFVar_x3f(x_205, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_206);
x_223 = l_Lean_Meta_Sym_getMaxFVar_x3f(x_206, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec_ref(x_223);
x_225 = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(x_222, x_224, x_4, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
x_129 = x_225;
goto block_156;
}
else
{
lean_dec(x_222);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_129 = x_223;
goto block_156;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_129 = x_221;
goto block_156;
}
}
}
}
}
case 6:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_1, 1);
x_230 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_230);
lean_inc_ref(x_229);
x_117 = x_229;
x_118 = x_230;
x_119 = x_2;
x_120 = x_3;
x_121 = x_4;
x_122 = x_5;
x_123 = x_6;
x_124 = x_7;
x_125 = lean_box(0);
goto block_128;
}
case 7:
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_1, 1);
x_232 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_232);
lean_inc_ref(x_231);
x_117 = x_231;
x_118 = x_232;
x_119 = x_2;
x_120 = x_3;
x_121 = x_4;
x_122 = x_5;
x_123 = x_6;
x_124 = x_7;
x_125 = lean_box(0);
goto block_128;
}
case 8:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; uint8_t x_260; 
x_233 = lean_ctor_get(x_1, 1);
x_234 = lean_ctor_get(x_1, 2);
x_235 = lean_ctor_get(x_1, 3);
x_260 = l_Lean_Expr_hasFVar(x_1);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = l_Lean_Expr_hasMVar(x_1);
x_236 = x_261;
goto block_259;
}
else
{
x_236 = x_260;
goto block_259;
}
block_259:
{
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; 
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_237 = lean_box(0);
x_238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_238, 0, x_237);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_st_ref_get(x_3);
x_240 = lean_ctor_get(x_239, 1);
lean_inc_ref(x_240);
lean_dec(x_239);
x_241 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(x_240, x_1);
if (lean_obj_tag(x_241) == 1)
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_249; 
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_242 = lean_ctor_get(x_241, 0);
x_249 = !lean_is_exclusive(x_241);
if (x_249 == 0)
{
x_243 = x_241;
x_244 = x_249;
goto block_248;
}
else
{
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_box(0);
x_244 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_245; 
if (x_244 == 0)
{
lean_ctor_set_tag(x_243, 0);
x_245 = x_243;
goto block_246;
}
else
{
lean_object* x_247; 
x_247 = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* x_250; 
lean_dec(x_241);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_233);
x_250 = l_Lean_Meta_Sym_getMaxFVar_x3f(x_233, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_234);
x_252 = l_Lean_Meta_Sym_getMaxFVar_x3f(x_234, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
lean_inc_ref(x_4);
x_254 = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(x_251, x_253, x_4, x_6, x_7);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_235);
x_256 = l_Lean_Meta_Sym_getMaxFVar_x3f(x_235, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(x_255, x_257, x_4, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
x_9 = x_258;
goto block_36;
}
else
{
lean_dec(x_255);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_9 = x_256;
goto block_36;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_9 = x_254;
goto block_36;
}
}
else
{
lean_dec(x_251);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_9 = x_252;
goto block_36;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_9 = x_250;
goto block_36;
}
}
}
}
}
case 10:
{
lean_object* x_262; uint8_t x_263; uint8_t x_305; 
x_262 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_262);
lean_dec_ref(x_1);
x_305 = l_Lean_Expr_hasFVar(x_262);
if (x_305 == 0)
{
uint8_t x_306; 
x_306 = l_Lean_Expr_hasMVar(x_262);
x_263 = x_306;
goto block_304;
}
else
{
x_263 = x_305;
goto block_304;
}
block_304:
{
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
lean_dec_ref(x_262);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_264 = lean_box(0);
x_265 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_265, 0, x_264);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_st_ref_get(x_3);
x_267 = lean_ctor_get(x_266, 1);
lean_inc_ref(x_267);
lean_dec(x_266);
x_268 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(x_267, x_262);
if (lean_obj_tag(x_268) == 1)
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; uint8_t x_276; 
lean_dec_ref(x_262);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_269 = lean_ctor_get(x_268, 0);
x_276 = !lean_is_exclusive(x_268);
if (x_276 == 0)
{
x_270 = x_268;
x_271 = x_276;
goto block_275;
}
else
{
lean_inc(x_269);
lean_dec(x_268);
x_270 = lean_box(0);
x_271 = x_276;
goto block_275;
}
block_275:
{
lean_object* x_272; 
if (x_271 == 0)
{
lean_ctor_set_tag(x_270, 0);
x_272 = x_270;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_274, 0, x_269);
x_272 = x_274;
goto block_273;
}
block_273:
{
return x_272;
}
}
}
else
{
lean_object* x_277; 
lean_dec(x_268);
lean_inc(x_3);
lean_inc_ref(x_262);
x_277 = l_Lean_Meta_Sym_getMaxFVar_x3f(x_262, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; uint8_t x_303; 
x_278 = lean_ctor_get(x_277, 0);
x_303 = !lean_is_exclusive(x_277);
if (x_303 == 0)
{
x_279 = x_277;
x_280 = x_303;
goto block_302;
}
else
{
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_box(0);
x_280 = x_303;
goto block_302;
}
block_302:
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; uint8_t x_291; uint8_t x_301; 
x_281 = lean_st_ref_take(x_3);
x_282 = lean_ctor_get(x_281, 0);
x_283 = lean_ctor_get(x_281, 1);
x_284 = lean_ctor_get(x_281, 2);
x_285 = lean_ctor_get(x_281, 3);
x_286 = lean_ctor_get(x_281, 4);
x_287 = lean_ctor_get(x_281, 5);
x_288 = lean_ctor_get(x_281, 6);
x_289 = lean_ctor_get_uint8(x_281, sizeof(void*)*7);
x_301 = !lean_is_exclusive(x_281);
if (x_301 == 0)
{
x_290 = x_281;
x_291 = x_301;
goto block_300;
}
else
{
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_281);
x_290 = lean_box(0);
x_291 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_292; lean_object* x_293; 
lean_inc(x_278);
x_292 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(x_283, x_262, x_278);
if (x_291 == 0)
{
lean_ctor_set(x_290, 1, x_292);
x_293 = x_290;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_299, 0, x_282);
lean_ctor_set(x_299, 1, x_292);
lean_ctor_set(x_299, 2, x_284);
lean_ctor_set(x_299, 3, x_285);
lean_ctor_set(x_299, 4, x_286);
lean_ctor_set(x_299, 5, x_287);
lean_ctor_set(x_299, 6, x_288);
lean_ctor_set_uint8(x_299, sizeof(void*)*7, x_289);
x_293 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_st_ref_set(x_3, x_293);
lean_dec(x_3);
if (x_280 == 0)
{
x_295 = x_279;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_278);
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
else
{
lean_dec_ref(x_262);
lean_dec(x_3);
return x_277;
}
}
}
}
}
case 11:
{
lean_object* x_307; uint8_t x_308; uint8_t x_350; 
x_307 = lean_ctor_get(x_1, 2);
x_350 = l_Lean_Expr_hasFVar(x_1);
if (x_350 == 0)
{
uint8_t x_351; 
x_351 = l_Lean_Expr_hasMVar(x_1);
x_308 = x_351;
goto block_349;
}
else
{
x_308 = x_350;
goto block_349;
}
block_349:
{
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; 
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_309 = lean_box(0);
x_310 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_310, 0, x_309);
return x_310;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_st_ref_get(x_3);
x_312 = lean_ctor_get(x_311, 1);
lean_inc_ref(x_312);
lean_dec(x_311);
x_313 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(x_312, x_1);
if (lean_obj_tag(x_313) == 1)
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; uint8_t x_321; 
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_314 = lean_ctor_get(x_313, 0);
x_321 = !lean_is_exclusive(x_313);
if (x_321 == 0)
{
x_315 = x_313;
x_316 = x_321;
goto block_320;
}
else
{
lean_inc(x_314);
lean_dec(x_313);
x_315 = lean_box(0);
x_316 = x_321;
goto block_320;
}
block_320:
{
lean_object* x_317; 
if (x_316 == 0)
{
lean_ctor_set_tag(x_315, 0);
x_317 = x_315;
goto block_318;
}
else
{
lean_object* x_319; 
x_319 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_319, 0, x_314);
x_317 = x_319;
goto block_318;
}
block_318:
{
return x_317;
}
}
}
else
{
lean_object* x_322; 
lean_dec(x_313);
lean_inc(x_3);
lean_inc_ref(x_307);
x_322 = l_Lean_Meta_Sym_getMaxFVar_x3f(x_307, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; uint8_t x_348; 
x_323 = lean_ctor_get(x_322, 0);
x_348 = !lean_is_exclusive(x_322);
if (x_348 == 0)
{
x_324 = x_322;
x_325 = x_348;
goto block_347;
}
else
{
lean_inc(x_323);
lean_dec(x_322);
x_324 = lean_box(0);
x_325 = x_348;
goto block_347;
}
block_347:
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; uint8_t x_336; uint8_t x_346; 
x_326 = lean_st_ref_take(x_3);
x_327 = lean_ctor_get(x_326, 0);
x_328 = lean_ctor_get(x_326, 1);
x_329 = lean_ctor_get(x_326, 2);
x_330 = lean_ctor_get(x_326, 3);
x_331 = lean_ctor_get(x_326, 4);
x_332 = lean_ctor_get(x_326, 5);
x_333 = lean_ctor_get(x_326, 6);
x_334 = lean_ctor_get_uint8(x_326, sizeof(void*)*7);
x_346 = !lean_is_exclusive(x_326);
if (x_346 == 0)
{
x_335 = x_326;
x_336 = x_346;
goto block_345;
}
else
{
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_326);
x_335 = lean_box(0);
x_336 = x_346;
goto block_345;
}
block_345:
{
lean_object* x_337; lean_object* x_338; 
lean_inc(x_323);
x_337 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(x_328, x_1, x_323);
if (x_336 == 0)
{
lean_ctor_set(x_335, 1, x_337);
x_338 = x_335;
goto block_343;
}
else
{
lean_object* x_344; 
x_344 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_344, 0, x_327);
lean_ctor_set(x_344, 1, x_337);
lean_ctor_set(x_344, 2, x_329);
lean_ctor_set(x_344, 3, x_330);
lean_ctor_set(x_344, 4, x_331);
lean_ctor_set(x_344, 5, x_332);
lean_ctor_set(x_344, 6, x_333);
lean_ctor_set_uint8(x_344, sizeof(void*)*7, x_334);
x_338 = x_344;
goto block_343;
}
block_343:
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_st_ref_set(x_3, x_338);
lean_dec(x_3);
if (x_325 == 0)
{
x_340 = x_324;
goto block_341;
}
else
{
lean_object* x_342; 
x_342 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_342, 0, x_323);
x_340 = x_342;
goto block_341;
}
block_341:
{
return x_340;
}
}
}
}
}
else
{
lean_dec_ref(x_1);
lean_dec(x_3);
return x_322;
}
}
}
}
}
default: 
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_352 = lean_box(0);
x_353 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_353, 0, x_352);
return x_353;
}
}
block_36:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_35; 
x_10 = lean_ctor_get(x_9, 0);
x_35 = !lean_is_exclusive(x_9);
if (x_35 == 0)
{
x_11 = x_9;
x_12 = x_35;
goto block_34;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_33; 
x_13 = lean_st_ref_take(x_3);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 2);
x_17 = lean_ctor_get(x_13, 3);
x_18 = lean_ctor_get(x_13, 4);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get_uint8(x_13, sizeof(void*)*7);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
x_22 = x_13;
x_23 = x_33;
goto block_32;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_22 = lean_box(0);
x_23 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_10);
x_24 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(x_15, x_1, x_10);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_24);
x_25 = x_22;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_16);
lean_ctor_set(x_31, 3, x_17);
lean_ctor_set(x_31, 4, x_18);
lean_ctor_set(x_31, 5, x_19);
lean_ctor_set(x_31, 6, x_20);
lean_ctor_set_uint8(x_31, sizeof(void*)*7, x_21);
x_25 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_st_ref_set(x_3, x_25);
lean_dec(x_3);
if (x_12 == 0)
{
x_27 = x_11;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_10);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
block_58:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; uint8_t x_57; 
x_39 = lean_st_ref_take(x_3);
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_ctor_get(x_39, 1);
x_42 = lean_ctor_get(x_39, 2);
x_43 = lean_ctor_get(x_39, 3);
x_44 = lean_ctor_get(x_39, 4);
x_45 = lean_ctor_get(x_39, 5);
x_46 = lean_ctor_get(x_39, 6);
x_47 = lean_ctor_get_uint8(x_39, sizeof(void*)*7);
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
x_48 = x_39;
x_49 = x_57;
goto block_56;
}
else
{
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_39);
x_48 = lean_box(0);
x_49 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_50; lean_object* x_51; 
lean_inc(x_37);
x_50 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(x_41, x_1, x_37);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_50);
x_51 = x_48;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_55, 0, x_40);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_55, 2, x_42);
lean_ctor_set(x_55, 3, x_43);
lean_ctor_set(x_55, 4, x_44);
lean_ctor_set(x_55, 5, x_45);
lean_ctor_set(x_55, 6, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*7, x_47);
x_51 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_st_ref_set(x_3, x_51);
lean_dec(x_3);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_37);
return x_53;
}
}
}
block_87:
{
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_86; 
x_61 = lean_ctor_get(x_60, 0);
x_86 = !lean_is_exclusive(x_60);
if (x_86 == 0)
{
x_62 = x_60;
x_63 = x_86;
goto block_85;
}
else
{
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_box(0);
x_63 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; uint8_t x_74; uint8_t x_84; 
x_64 = lean_st_ref_take(x_59);
x_65 = lean_ctor_get(x_64, 0);
x_66 = lean_ctor_get(x_64, 1);
x_67 = lean_ctor_get(x_64, 2);
x_68 = lean_ctor_get(x_64, 3);
x_69 = lean_ctor_get(x_64, 4);
x_70 = lean_ctor_get(x_64, 5);
x_71 = lean_ctor_get(x_64, 6);
x_72 = lean_ctor_get_uint8(x_64, sizeof(void*)*7);
x_84 = !lean_is_exclusive(x_64);
if (x_84 == 0)
{
x_73 = x_64;
x_74 = x_84;
goto block_83;
}
else
{
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_64);
x_73 = lean_box(0);
x_74 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_75; lean_object* x_76; 
lean_inc(x_61);
x_75 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(x_66, x_1, x_61);
if (x_74 == 0)
{
lean_ctor_set(x_73, 1, x_75);
x_76 = x_73;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_82, 0, x_65);
lean_ctor_set(x_82, 1, x_75);
lean_ctor_set(x_82, 2, x_67);
lean_ctor_set(x_82, 3, x_68);
lean_ctor_set(x_82, 4, x_69);
lean_ctor_set(x_82, 5, x_70);
lean_ctor_set(x_82, 6, x_71);
lean_ctor_set_uint8(x_82, sizeof(void*)*7, x_72);
x_76 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_st_ref_set(x_59, x_76);
lean_dec(x_59);
if (x_63 == 0)
{
x_78 = x_62;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_61);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
else
{
lean_dec(x_59);
lean_dec_ref(x_1);
return x_60;
}
}
block_116:
{
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_96);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec_ref(x_1);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_st_ref_get(x_91);
x_101 = lean_ctor_get(x_100, 1);
lean_inc_ref(x_101);
lean_dec(x_100);
x_102 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(x_101, x_1);
if (lean_obj_tag(x_102) == 1)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_dec_ref(x_96);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec_ref(x_1);
x_103 = lean_ctor_get(x_102, 0);
x_110 = !lean_is_exclusive(x_102);
if (x_110 == 0)
{
x_104 = x_102;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_box(0);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_105 == 0)
{
lean_ctor_set_tag(x_104, 0);
x_106 = x_104;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* x_111; 
lean_dec(x_102);
lean_inc(x_89);
lean_inc_ref(x_88);
lean_inc(x_92);
lean_inc_ref(x_90);
lean_inc(x_91);
lean_inc_ref(x_96);
x_111 = l_Lean_Meta_Sym_getMaxFVar_x3f(x_94, x_96, x_91, x_90, x_92, x_88, x_89);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
lean_inc(x_89);
lean_inc_ref(x_88);
lean_inc_ref(x_90);
lean_inc(x_91);
x_113 = l_Lean_Meta_Sym_getMaxFVar_x3f(x_93, x_96, x_91, x_90, x_92, x_88, x_89);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = l___private_Lean_Meta_Sym_MaxFVar_0__Lean_Meta_Sym_max___redArg(x_112, x_114, x_90, x_88, x_89);
lean_dec(x_89);
lean_dec_ref(x_88);
x_59 = x_91;
x_60 = x_115;
goto block_87;
}
else
{
lean_dec(x_112);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
x_59 = x_91;
x_60 = x_113;
goto block_87;
}
}
else
{
lean_dec_ref(x_96);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
x_59 = x_91;
x_60 = x_111;
goto block_87;
}
}
}
}
block_128:
{
uint8_t x_126; 
x_126 = l_Lean_Expr_hasFVar(x_1);
if (x_126 == 0)
{
uint8_t x_127; 
x_127 = l_Lean_Expr_hasMVar(x_1);
x_88 = x_123;
x_89 = x_124;
x_90 = x_121;
x_91 = x_120;
x_92 = x_122;
x_93 = x_118;
x_94 = x_117;
x_95 = lean_box(0);
x_96 = x_119;
x_97 = x_127;
goto block_116;
}
else
{
x_88 = x_123;
x_89 = x_124;
x_90 = x_121;
x_91 = x_120;
x_92 = x_122;
x_93 = x_118;
x_94 = x_117;
x_95 = lean_box(0);
x_96 = x_119;
x_97 = x_126;
goto block_116;
}
}
block_156:
{
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_155; 
x_130 = lean_ctor_get(x_129, 0);
x_155 = !lean_is_exclusive(x_129);
if (x_155 == 0)
{
x_131 = x_129;
x_132 = x_155;
goto block_154;
}
else
{
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_box(0);
x_132 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; uint8_t x_143; uint8_t x_153; 
x_133 = lean_st_ref_take(x_3);
x_134 = lean_ctor_get(x_133, 0);
x_135 = lean_ctor_get(x_133, 1);
x_136 = lean_ctor_get(x_133, 2);
x_137 = lean_ctor_get(x_133, 3);
x_138 = lean_ctor_get(x_133, 4);
x_139 = lean_ctor_get(x_133, 5);
x_140 = lean_ctor_get(x_133, 6);
x_141 = lean_ctor_get_uint8(x_133, sizeof(void*)*7);
x_153 = !lean_is_exclusive(x_133);
if (x_153 == 0)
{
x_142 = x_133;
x_143 = x_153;
goto block_152;
}
else
{
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_133);
x_142 = lean_box(0);
x_143 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_144; lean_object* x_145; 
lean_inc(x_130);
x_144 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(x_135, x_1, x_130);
if (x_143 == 0)
{
lean_ctor_set(x_142, 1, x_144);
x_145 = x_142;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_151, 0, x_134);
lean_ctor_set(x_151, 1, x_144);
lean_ctor_set(x_151, 2, x_136);
lean_ctor_set(x_151, 3, x_137);
lean_ctor_set(x_151, 4, x_138);
lean_ctor_set(x_151, 5, x_139);
lean_ctor_set(x_151, 6, x_140);
lean_ctor_set_uint8(x_151, sizeof(void*)*7, x_141);
x_145 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_st_ref_set(x_3, x_145);
lean_dec(x_3);
if (x_132 == 0)
{
x_147 = x_131;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_130);
x_147 = x_149;
goto block_148;
}
block_148:
{
return x_147;
}
}
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Sym_getMaxFVar_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__1_spec__2_spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getMaxFVar_x3f_spec__0_spec__0_spec__2_spec__4___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin)
;
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
res = initialize_Lean_Meta_Sym_SymM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_MaxFVar(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_MaxFVar(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_MaxFVar(builtin);
}
#ifdef __cplusplus
}
#endif
