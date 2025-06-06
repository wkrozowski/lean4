// Lean compiler output
// Module: Init.Data.Array.Set
// Imports: Init.Tactics
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
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17_;
LEAN_EXPORT lean_object* l_Array_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_setIfInBounds___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__16;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__9;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__22;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__12;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__11;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__3;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__18;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__1;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__21;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__7;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__17;
LEAN_EXPORT lean_object* l_Array_setIfInBounds___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__19;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__8;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__15;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__10;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__4;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__20;
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__14;
LEAN_EXPORT lean_object* l_Array_setIfInBounds(lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__13;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__2;
LEAN_EXPORT lean_object* l_Array_set_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Set___hyg_17____closed__6;
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__1;
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__2;
x_3 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__3;
x_4 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__1;
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__2;
x_3 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__3;
x_4 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticGet_elem_tactic", 21, 21);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("get_elem_tactic", 15, 15);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__13;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__6;
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__12;
x_3 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__15;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__6;
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__16;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__10;
x_3 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__17;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__6;
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__18;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__8;
x_3 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__19;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__6;
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__20;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__5;
x_3 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__21;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Set___hyg_17_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_Data_Array_Set___hyg_17____closed__22;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_array_fset(x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_setIfInBounds___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_6; 
x_6 = lean_array_fset(x_1, x_2, x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_setIfInBounds(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_setIfInBounds___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_setIfInBounds___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_setIfInBounds___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_set_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_set(x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Set(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__1 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__1();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__1);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__2 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__2();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__2);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__3 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__3();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__3);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__4 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__4();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__4);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__5 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__5();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__5);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__6 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__6();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__6);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__7 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__7();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__7);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__8 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__8();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__8);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__9 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__9();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__9);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__10 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__10();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__10);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__11 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__11();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__11);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__12 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__12();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__12);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__13 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__13();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__13);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__14 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__14();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__14);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__15 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__15();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__15);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__16 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__16();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__16);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__17 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__17();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__17);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__18 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__18();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__18);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__19 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__19();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__19);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__20 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__20();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__20);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__21 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__21();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__21);
l___auto____x40_Init_Data_Array_Set___hyg_17____closed__22 = _init_l___auto____x40_Init_Data_Array_Set___hyg_17____closed__22();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17____closed__22);
l___auto____x40_Init_Data_Array_Set___hyg_17_ = _init_l___auto____x40_Init_Data_Array_Set___hyg_17_();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Set___hyg_17_);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
