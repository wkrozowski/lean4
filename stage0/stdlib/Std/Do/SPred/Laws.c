// Lean compiler output
// Module: Std.Do.SPred.Laws
// Imports: Std.Do.SPred.Notation
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_5);
x_6 = lean_apply_2(x_4, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_4(x_5, lean_box(0), x_7, x_2, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Do_SPred_Laws_0__Std_Do_SPred_entails_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Do_SPred_instTransEntails(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Do_SPred_instTransBientails(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Std_Do_SPred_Notation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_SPred_Laws(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_SPred_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
