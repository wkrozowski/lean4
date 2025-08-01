// Lean compiler output
// Module: Lean.Compiler.NoncomputableAttr
// Imports: Lean.EnvExtension
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
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Compiler_NoncomputableAttr___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_noncomputableExt;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Compiler_NoncomputableAttr___hyg_4_;
LEAN_EXPORT uint8_t l_Lean_isNoncomputable(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addNoncomputable(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isNoncomputable___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_NoncomputableAttr___hyg_4_(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Compiler_NoncomputableAttr___hyg_4_;
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addNoncomputable___closed__0;
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, uint8_t, lean_object*);
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Compiler_NoncomputableAttr___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Compiler_NoncomputableAttr___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("noncomputableExt", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Compiler_NoncomputableAttr___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_Compiler_NoncomputableAttr___hyg_4_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_Compiler_NoncomputableAttr___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_NoncomputableAttr___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_Compiler_NoncomputableAttr___hyg_4_;
x_3 = 2;
x_4 = l_Lean_mkTagDeclarationExtension(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_addNoncomputable___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_noncomputableExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addNoncomputable(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_addNoncomputable___closed__0;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isNoncomputable(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_addNoncomputable___closed__0;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isNoncomputable___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isNoncomputable(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__0____x40_Lean_Compiler_NoncomputableAttr___hyg_4_ = _init_l_Lean_initFn___closed__0____x40_Lean_Compiler_NoncomputableAttr___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Compiler_NoncomputableAttr___hyg_4_);
l_Lean_initFn___closed__1____x40_Lean_Compiler_NoncomputableAttr___hyg_4_ = _init_l_Lean_initFn___closed__1____x40_Lean_Compiler_NoncomputableAttr___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Compiler_NoncomputableAttr___hyg_4_);
l_Lean_initFn___closed__2____x40_Lean_Compiler_NoncomputableAttr___hyg_4_ = _init_l_Lean_initFn___closed__2____x40_Lean_Compiler_NoncomputableAttr___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Compiler_NoncomputableAttr___hyg_4_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Compiler_NoncomputableAttr___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_noncomputableExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_noncomputableExt);
lean_dec_ref(res);
}l_Lean_addNoncomputable___closed__0 = _init_l_Lean_addNoncomputable___closed__0();
lean_mark_persistent(l_Lean_addNoncomputable___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
