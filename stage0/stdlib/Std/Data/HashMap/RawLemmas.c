// Lean compiler output
// Module: Std.Data.HashMap.RawLemmas
// Imports: Std.Data.DHashMap.RawLemmas Std.Data.HashMap.Raw Std.Data.DHashMap.Raw
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Equiv_instTrans(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Equiv_instTrans(lean_object* x_1, lean_object* x_2) {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Std_Data_DHashMap_RawLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_DHashMap_Raw(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashMap_RawLemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_RawLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Raw(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Raw(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
