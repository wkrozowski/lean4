// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers
// Imports: Std.Data.Iterators.Lemmas.Producers.Monadic Std.Data.Iterators.Lemmas.Producers.Array Std.Data.Iterators.Lemmas.Producers.Empty Std.Data.Iterators.Lemmas.Producers.List Std.Data.Iterators.Lemmas.Producers.Repeat Std.Data.Iterators.Lemmas.Producers.Range Std.Data.Iterators.Lemmas.Producers.Slice
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
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Monadic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Array(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Empty(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_List(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Repeat(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Range(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Slice(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Producers(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Producers_Array(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Producers_Empty(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Producers_List(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Producers_Repeat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Producers_Range(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Producers_Slice(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
