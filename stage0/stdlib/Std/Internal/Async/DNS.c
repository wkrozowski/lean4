// Lean compiler output
// Module: Std.Internal.Async.DNS
// Imports: public import Std.Time public import Std.Internal.UV public import Std.Internal.Async.Basic public import Init.Data.Function
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
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0_value;
static const lean_closure_object l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0_value)} };
static const lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__1_value;
static const lean_closure_object l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__1_value)} };
static const lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__2 = (const lean_object*)&l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__2_value;
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_dns_get_info(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_DNS_getNameInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_DNS_getNameInfo___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_DNS_getNameInfo___closed__0_value;
lean_object* l_Function_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_DNS_getNameInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_uncurry, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_IO_Async_DNS_getNameInfo___closed__0_value)} };
static const lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_DNS_getNameInfo___closed__1_value;
static const lean_closure_object l_Std_Internal_IO_Async_DNS_getNameInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0_value)} };
static const lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___closed__2 = (const lean_object*)&l_Std_Internal_IO_Async_DNS_getNameInfo___closed__2_value;
static const lean_closure_object l_Std_Internal_IO_Async_DNS_getNameInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_DNS_getNameInfo___closed__2_value)} };
static const lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___closed__3 = (const lean_object*)&l_Std_Internal_IO_Async_DNS_getNameInfo___closed__3_value;
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_DNS_getNameInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_IO_Async_DNS_getNameInfo___closed__1_value)} };
static const lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___closed__4 = (const lean_object*)&l_Std_Internal_IO_Async_DNS_getNameInfo___closed__4_value;
lean_object* lean_uv_dns_get_name(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_7 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec_ref(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_22; 
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_13, 0);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
x_15 = x_13;
x_16 = x_22;
goto block_21;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_14);
x_17 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec_ref(x_13);
x_24 = lean_io_promise_result_opt(x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = 0;
x_27 = lean_task_map(x_1, x_24, x_25, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_14; 
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_34; 
x_34 = 0;
x_14 = x_34;
goto block_33;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_unbox(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = 1;
x_14 = x_37;
goto block_33;
}
else
{
uint8_t x_38; 
x_38 = 2;
x_14 = x_38;
goto block_33;
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_11, x_9, x_5);
return x_12;
}
block_33:
{
lean_object* x_15; lean_object* x_16; 
x_15 = ((lean_object*)(l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__2));
x_16 = lean_uv_dns_get_info(x_1, x_2, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
x_18 = x_16;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 1);
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
x_5 = x_15;
x_6 = x_20;
x_7 = lean_box(0);
goto block_13;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_25 = lean_ctor_get(x_16, 0);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
x_26 = x_16;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 0);
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
x_5 = x_15;
x_6 = x_28;
x_7 = lean_box(0);
goto block_13;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_DNS_getAddrInfo(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_7 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec_ref(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_22; 
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_13, 0);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
x_15 = x_13;
x_16 = x_22;
goto block_21;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_14);
x_17 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec_ref(x_13);
x_24 = lean_io_promise_result_opt(x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = 0;
x_27 = lean_task_map(x_1, x_24, x_25, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_52; 
x_7 = ((lean_object*)(l_Std_Internal_IO_Async_DNS_getNameInfo___closed__3));
x_52 = lean_uv_dns_get_name(x_1);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
x_53 = lean_ctor_get(x_52, 0);
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
x_54 = x_52;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
lean_ctor_set_tag(x_54, 1);
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
x_8 = x_56;
x_9 = lean_box(0);
goto block_51;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
x_61 = lean_ctor_get(x_52, 0);
x_68 = !lean_is_exclusive(x_52);
if (x_68 == 0)
{
x_62 = x_52;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_52);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
lean_ctor_set_tag(x_62, 0);
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
x_8 = x_64;
x_9 = lean_box(0);
goto block_51;
}
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
block_51:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_12, x_13, x_11, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
x_17 = x_15;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
x_3 = lean_box(0);
x_4 = x_19;
goto block_6;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_40; 
x_24 = lean_ctor_get(x_15, 0);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
x_25 = x_15;
x_26 = x_40;
goto block_39;
}
else
{
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_38; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
x_29 = x_24;
x_30 = x_38;
goto block_37;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_28);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_31);
x_32 = x_25;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_3 = lean_box(0);
x_4 = x_32;
goto block_6;
}
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_50; 
x_41 = lean_ctor_get(x_14, 0);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
x_42 = x_14;
x_43 = x_50;
goto block_49;
}
else
{
lean_inc(x_41);
lean_dec(x_14);
x_42 = lean_box(0);
x_43 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = ((lean_object*)(l_Std_Internal_IO_Async_DNS_getNameInfo___closed__4));
x_45 = lean_task_map(x_44, x_41, x_12, x_13);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_45);
x_46 = x_42;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_DNS_getNameInfo(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Async_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Function(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Async_DNS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Async_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Function(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Async_DNS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Function(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_DNS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Function(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Async_DNS(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Async_DNS(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Async_DNS(builtin);
}
#ifdef __cplusplus
}
#endif
