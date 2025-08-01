// Lean compiler output
// Module: Init.Data.Option.Attach
// Imports: Init.Data.Option.Basic Init.Data.Option.List Init.Data.Option.Array Init.Data.Array.Attach Init.Data.List.Attach Init.BinderPredicates
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_attach___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_attach___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_attach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_unattach___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_unattach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_attach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_unattach___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_unattach___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Option_attach___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Option_attach(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_attach___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_attach___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_attach___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_attach(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_unattach___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Option_unattach(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_unattach___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_unattach___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_unattach___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_unattach(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Option_List(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Option_Array(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin, lean_object*);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Attach(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_List(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Array(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
