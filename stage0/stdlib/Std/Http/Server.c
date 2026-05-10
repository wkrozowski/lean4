// Lean compiler output
// Module: Std.Http.Server
// Imports: public import Std.Async public import Std.Async.TCP public import Std.Sync.CancellationToken public import Std.Sync.Semaphore public import Std.Http.Server.Config public import Std.Http.Server.Handler public import Std.Http.Server.Connection
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
lean_object* l_Std_Semaphore_release(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Http_Extensions_empty;
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Std_Http_instTransportClient;
lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
lean_object* l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_fork(lean_object*);
extern lean_object* l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_getpeername(lean_object*);
lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* l_Std_Semaphore_acquire(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l___private_Init_While_0__whileM_erased___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Async_ContextAsync_instMonad;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_uv_tcp_nodelay(lean_object*);
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t);
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*);
lean_object* lean_uv_tcp_new();
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* l_Std_CancellationContext_new();
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l_Std_CloseableChannel_new___redArg(lean_object*);
lean_object* l_Std_Semaphore_new(lean_object*);
lean_object* l_Std_Channel_recv___redArg(lean_object*, lean_object*);
lean_object* l_Std_Channel_recvSelector___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_new(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_new___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_waitShutdown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_waitShutdown___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_waitShutdown___closed__0 = (const lean_object*)&l_Std_Http_Server_waitShutdown___closed__0_value;
static const lean_closure_object l_Std_Http_Server_waitShutdown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_waitShutdown___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Server_waitShutdown___closed__0_value)} };
static const lean_object* l_Std_Http_Server_waitShutdown___closed__1 = (const lean_object*)&l_Std_Http_Server_waitShutdown___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdownSelector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value),((lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value)} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value;
static const lean_closure_object l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6 = (const lean_object*)&l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object*);
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__4___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Std_Http_Server_serve___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Server_serve___redArg___lam__4___closed__0_value)}};
static const lean_object* l_Std_Http_Server_serve___redArg___lam__4___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__21___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__21___closed__0;
static lean_once_cell_t l_Std_Http_Server_serve___redArg___lam__21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serve___redArg___lam__21___closed__1;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Extensions_compareName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__21___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__21___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__9___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__29___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__29___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___lam__29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__6___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Server_serve___redArg___lam__29___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___lam__29___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object**);
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__0 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__1 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__2 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__3 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__4 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__4_value;
static const lean_closure_object l_Std_Http_Server_serve___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_serve___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_serve___redArg___closed__5 = (const lean_object*)&l_Std_Http_Server_serve___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_new(lean_object* v_config_1_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_connectionLimit_7_; lean_object* v_maxConnections_12_; uint8_t v___x_13_; 
v___x_3_ = l_Std_CancellationContext_new();
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = l_Std_Mutex_new___redArg(v___x_4_);
v_maxConnections_12_ = lean_ctor_get(v_config_1_, 0);
v___x_13_ = lean_nat_dec_eq(v_maxConnections_12_, v___x_4_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_inc(v_maxConnections_12_);
v___x_14_ = l_Std_Semaphore_new(v_maxConnections_12_);
v___x_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
v_connectionLimit_7_ = v___x_15_;
goto v___jp_6_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
v_connectionLimit_7_ = v___x_16_;
goto v___jp_6_;
}
v___jp_6_:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_8_ = lean_box(0);
v___x_9_ = l_Std_CloseableChannel_new___redArg(v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v___x_3_);
lean_ctor_set(v___x_10_, 1, v___x_5_);
lean_ctor_set(v___x_10_, 2, v_connectionLimit_7_);
lean_ctor_set(v___x_10_, 3, v___x_9_);
lean_ctor_set(v___x_10_, 4, v_config_1_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_new___boxed(lean_object* v_config_17_, lean_object* v_a_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Http_Server_new(v_config_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown(lean_object* v_s_20_){
_start:
{
lean_object* v_context_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_context_22_ = lean_ctor_get(v_s_20_, 0);
lean_inc_ref(v_context_22_);
lean_dec_ref(v_s_20_);
v___x_23_ = lean_box(1);
v___x_24_ = l_Std_CancellationContext_cancel(v_context_22_, v___x_23_);
v___x_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdown___boxed(lean_object* v_s_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Http_Server_shutdown(v_s_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__0(lean_object* v_a_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_31_, 0, v_a_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__1(lean_object* v___f_32_, lean_object* v_x_33_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
lean_dec_ref(v___f_32_);
v_a_35_ = lean_ctor_get(v_x_33_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v_x_33_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v_x_33_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v_x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_35_);
v___x_40_ = v_reuseFailAlloc_42_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; 
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
}
else
{
lean_object* v_a_44_; lean_object* v___x_45_; uint8_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_a_44_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_a_44_);
lean_dec_ref(v_x_33_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = 0;
v___x_47_ = lean_task_map(v___f_32_, v_a_44_, v___x_45_, v___x_46_);
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___lam__1___boxed(lean_object* v___f_49_, lean_object* v_x_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Http_Server_waitShutdown___lam__1(v___f_49_, v_x_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown(lean_object* v_s_56_){
_start:
{
lean_object* v_shutdownPromise_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; 
v_shutdownPromise_58_ = lean_ctor_get(v_s_56_, 3);
lean_inc_ref(v_shutdownPromise_58_);
lean_dec_ref(v_s_56_);
v___x_59_ = lean_box(0);
v___x_60_ = l_Std_Channel_recv___redArg(v___x_59_, v_shutdownPromise_58_);
v___f_61_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__1));
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_60_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = 0;
v___x_66_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_64_, v___x_65_, v___x_63_, v___f_61_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdown___boxed(lean_object* v_s_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Std_Http_Server_waitShutdown(v_s_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_waitShutdownSelector(lean_object* v_s_70_){
_start:
{
lean_object* v_shutdownPromise_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_shutdownPromise_71_ = lean_ctor_get(v_s_70_, 3);
lean_inc_ref(v_shutdownPromise_71_);
lean_dec_ref(v_s_70_);
v___x_72_ = lean_box(0);
v___x_73_ = l_Std_Channel_recvSelector___redArg(v___x_72_, v_shutdownPromise_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__2(lean_object* v_shutdownPromise_74_, lean_object* v___f_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_78_; 
lean_dec_ref(v___f_75_);
lean_dec_ref(v_shutdownPromise_74_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v_x_76_);
return v___x_78_;
}
else
{
lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_91_; 
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v_x_76_, 0);
lean_dec(v_unused_92_);
v___x_80_ = v_x_76_;
v_isShared_81_ = v_isSharedCheck_91_;
goto v_resetjp_79_;
}
else
{
lean_dec(v_x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_91_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_82_ = lean_box(0);
v___x_83_ = l_Std_Channel_recv___redArg(v___x_82_, v_shutdownPromise_74_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_83_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_90_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; 
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = 0;
v___x_89_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_87_, v___x_88_, v___x_86_, v___f_75_);
return v___x_89_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___lam__2___boxed(lean_object* v_shutdownPromise_93_, lean_object* v___f_94_, lean_object* v_x_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_Http_Server_shutdownAndWait___lam__2(v_shutdownPromise_93_, v___f_94_, v_x_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait(lean_object* v_s_98_){
_start:
{
lean_object* v_context_100_; lean_object* v_shutdownPromise_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___f_104_; lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; 
v_context_100_ = lean_ctor_get(v_s_98_, 0);
lean_inc_ref(v_context_100_);
v_shutdownPromise_101_ = lean_ctor_get(v_s_98_, 3);
lean_inc_ref(v_shutdownPromise_101_);
lean_dec_ref(v_s_98_);
v___x_102_ = lean_box(1);
v___x_103_ = l_Std_CancellationContext_cancel(v_context_100_, v___x_102_);
v___f_104_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__1));
v___f_105_ = lean_alloc_closure((void*)(l_Std_Http_Server_shutdownAndWait___lam__2___boxed), 4, 2);
lean_closure_set(v___f_105_, 0, v_shutdownPromise_101_);
lean_closure_set(v___f_105_, 1, v___f_104_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_103_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = 0;
v___x_110_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_108_, v___x_109_, v___x_107_, v___f_105_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_shutdownAndWait___boxed(lean_object* v_s_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_Http_Server_shutdownAndWait(v_s_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_121_ = lean_st_ref_take(v___y_118_);
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_add(v___x_121_, v___x_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_st_ref_set(v___y_118_, v___x_123_);
v___x_125_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed(lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(v___y_126_, v___y_127_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_133_ = lean_st_ref_take(v___y_130_);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_sub(v___x_133_, v___x_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_st_ref_set(v___y_130_, v___x_135_);
v___x_137_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(v___y_138_, v___y_139_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(lean_object* v_a_142_, lean_object* v_shutdownPromise_143_, lean_object* v_x_144_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref(v_shutdownPromise_143_);
v_a_148_ = lean_ctor_get(v_x_144_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_144_);
if (v_isSharedCheck_156_ == 0)
{
v___x_150_ = v_x_144_;
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v_x_144_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_155_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_a_157_ = lean_ctor_get(v_x_144_, 0);
lean_inc(v_a_157_);
lean_dec_ref(v_x_144_);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_nat_dec_eq(v_a_142_, v___x_158_);
if (v___x_159_ == 0)
{
lean_dec(v_a_157_);
lean_dec_ref(v_shutdownPromise_143_);
goto v___jp_146_;
}
else
{
uint8_t v___x_160_; 
v___x_160_ = lean_unbox(v_a_157_);
lean_dec(v_a_157_);
if (v___x_160_ == 0)
{
lean_dec_ref(v_shutdownPromise_143_);
goto v___jp_146_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_box(0);
v___x_162_ = l_Std_Channel_send___redArg(v_shutdownPromise_143_, v___x_161_);
lean_dec_ref(v___x_162_);
v___x_163_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_163_;
}
}
}
v___jp_146_:
{
lean_object* v___x_147_; 
v___x_147_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(lean_object* v_a_164_, lean_object* v_shutdownPromise_165_, lean_object* v_x_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(v_a_164_, v_shutdownPromise_165_, v_x_166_);
lean_dec(v_a_164_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(lean_object* v_context_169_, lean_object* v_shutdownPromise_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_171_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
lean_dec_ref(v_shutdownPromise_170_);
lean_dec_ref(v_context_169_);
v_a_173_ = lean_ctor_get(v_x_171_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v_x_171_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v_x_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_180_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; 
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_197_; 
v_a_182_ = lean_ctor_get(v_x_171_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_197_ == 0)
{
v___x_184_ = v_x_171_;
v_isShared_185_ = v_isSharedCheck_197_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v_x_171_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_197_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_token_186_; uint8_t v___x_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v_token_186_ = lean_ctor_get(v_context_169_, 1);
lean_inc_ref(v_token_186_);
lean_dec_ref(v_context_169_);
v___x_187_ = l_Std_CancellationToken_isCancelled(v_token_186_);
v___f_188_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_188_, 0, v_a_182_);
lean_closure_set(v___f_188_, 1, v_shutdownPromise_170_);
v___x_189_ = lean_box(v___x_187_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_189_);
v___x_191_ = v___x_184_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_196_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; 
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = 0;
v___x_195_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_193_, v___x_194_, v___x_192_, v___f_188_);
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed(lean_object* v_context_198_, lean_object* v_shutdownPromise_199_, lean_object* v_x_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(v_context_198_, v_shutdownPromise_199_, v_x_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(lean_object* v___f_203_, lean_object* v_____r_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; 
v___x_208_ = lean_st_ref_get(v___y_205_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = 0;
v___x_213_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_211_, v___x_212_, v___x_210_, v___f_203_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(lean_object* v___f_214_, lean_object* v_____r_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(v___f_214_, v_____r_215_, v___y_216_, v___y_217_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(lean_object* v_x_220_){
_start:
{
lean_object* v_fst_221_; 
v_fst_221_ = lean_ctor_get(v_x_220_, 0);
lean_inc(v_fst_221_);
return v_fst_221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(lean_object* v_x_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(v_x_222_);
lean_dec_ref(v_x_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(lean_object* v___x_224_, lean_object* v___f_225_, lean_object* v___f_226_, lean_object* v___f_227_, lean_object* v___f_228_, lean_object* v_activeConnections_229_, lean_object* v_____r_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_2353__overap_234_; lean_object* v___x_235_; 
lean_inc_ref(v___x_224_);
v___x_233_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_233_, 0, lean_box(0));
lean_closure_set(v___x_233_, 1, lean_box(0));
lean_closure_set(v___x_233_, 2, lean_box(0));
lean_closure_set(v___x_233_, 3, v___x_224_);
lean_closure_set(v___x_233_, 4, lean_box(0));
lean_closure_set(v___x_233_, 5, lean_box(0));
lean_closure_set(v___x_233_, 6, v___f_225_);
lean_closure_set(v___x_233_, 7, v___f_226_);
v___x_2353__overap_234_ = l_Std_Mutex_atomically___redArg(v___x_224_, v___f_227_, v___f_228_, v_activeConnections_229_, v___x_233_);
lean_inc_ref(v___y_231_);
v___x_235_ = lean_apply_2(v___x_2353__overap_234_, v___y_231_, lean_box(0));
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed(lean_object* v___x_236_, lean_object* v___f_237_, lean_object* v___f_238_, lean_object* v___f_239_, lean_object* v___f_240_, lean_object* v_activeConnections_241_, lean_object* v_____r_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(v___x_236_, v___f_237_, v___f_238_, v___f_239_, v___f_240_, v_activeConnections_241_, v_____r_242_, v___y_243_);
lean_dec_ref(v___y_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(lean_object* v___f_246_, lean_object* v_a_247_, lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v___f_246_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v_x_248_);
return v___x_250_;
}
else
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v_x_248_, 0);
lean_inc(v_a_251_);
lean_dec_ref(v_x_248_);
lean_inc_ref(v_a_247_);
v___x_252_ = lean_apply_3(v___f_246_, v_a_251_, v_a_247_, lean_box(0));
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed(lean_object* v___f_253_, lean_object* v_a_254_, lean_object* v_x_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(v___f_253_, v_a_254_, v_x_255_);
lean_dec_ref(v_a_254_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(uint8_t v_releaseConnectionPermit_258_, lean_object* v___f_259_, lean_object* v_a_260_, lean_object* v_connectionLimit_261_, lean_object* v___f_262_, lean_object* v_opt_263_){
_start:
{
if (v_releaseConnectionPermit_258_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref(v___f_262_);
lean_dec(v_connectionLimit_261_);
v___x_265_ = lean_box(0);
lean_inc_ref(v_a_260_);
v___x_266_ = lean_apply_3(v___f_259_, v___x_265_, v_a_260_, lean_box(0));
return v___x_266_;
}
else
{
if (lean_obj_tag(v_connectionLimit_261_) == 1)
{
lean_object* v_val_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_279_; 
lean_dec_ref(v___f_259_);
v_val_267_ = lean_ctor_get(v_connectionLimit_261_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v_connectionLimit_261_);
if (v_isSharedCheck_279_ == 0)
{
v___x_269_ = v_connectionLimit_261_;
v_isShared_270_ = v_isSharedCheck_279_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_val_267_);
lean_dec(v_connectionLimit_261_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_279_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = l_Std_Semaphore_release(v_val_267_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_271_);
v___x_273_ = v___x_269_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_278_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; 
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = 0;
v___x_277_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_275_, v___x_276_, v___x_274_, v___f_262_);
return v___x_277_;
}
}
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec_ref(v___f_262_);
lean_dec(v_connectionLimit_261_);
v___x_280_ = lean_box(0);
lean_inc_ref(v_a_260_);
v___x_281_ = lean_apply_3(v___f_259_, v___x_280_, v_a_260_, lean_box(0));
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed(lean_object* v_releaseConnectionPermit_282_, lean_object* v___f_283_, lean_object* v_a_284_, lean_object* v_connectionLimit_285_, lean_object* v___f_286_, lean_object* v_opt_287_, lean_object* v___y_288_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_289_; lean_object* v_res_290_; 
v_releaseConnectionPermit_boxed_289_ = lean_unbox(v_releaseConnectionPermit_282_);
v_res_290_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(v_releaseConnectionPermit_boxed_289_, v___f_283_, v_a_284_, v_connectionLimit_285_, v___f_286_, v_opt_287_);
lean_dec(v_opt_287_);
lean_dec_ref(v_a_284_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(lean_object* v_action_291_, lean_object* v_a_292_, lean_object* v___f_293_, lean_object* v___f_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_305_; 
lean_dec(v___f_294_);
lean_dec_ref(v___f_293_);
lean_dec_ref(v_action_291_);
v_a_297_ = lean_ctor_get(v_x_295_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_x_295_);
if (v_isSharedCheck_305_ == 0)
{
v___x_299_ = v_x_295_;
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v_x_295_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_304_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___y_311_; 
lean_dec_ref(v_x_295_);
lean_inc_ref(v_a_292_);
v___x_306_ = lean_apply_1(v_action_291_, v_a_292_);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = 0;
v___x_309_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_306_, v___f_293_, v___x_307_, v___x_308_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_313_; 
lean_dec(v___f_294_);
v_a_313_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_313_);
lean_dec_ref(v___x_309_);
if (lean_obj_tag(v_a_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_314_ = lean_ctor_get(v_a_313_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_a_313_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v_a_313_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v_a_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
v___y_311_ = v___x_319_;
goto v___jp_310_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_330_; 
v_a_322_ = lean_ctor_get(v_a_313_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_a_313_);
if (v_isSharedCheck_330_ == 0)
{
v___x_324_ = v_a_313_;
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v_a_313_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v_fst_326_; lean_object* v___x_328_; 
v_fst_326_ = lean_ctor_get(v_a_322_, 0);
lean_inc(v_fst_326_);
lean_dec(v_a_322_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v_fst_326_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_fst_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v___y_311_ = v___x_328_;
goto v___jp_310_;
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_340_; 
v_a_331_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_340_ == 0)
{
v___x_333_ = v___x_309_;
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_309_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_335_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_335_, 0, lean_box(0));
lean_closure_set(v___x_335_, 1, lean_box(0));
lean_closure_set(v___x_335_, 2, lean_box(0));
lean_closure_set(v___x_335_, 3, v___f_294_);
v___x_336_ = lean_task_map(v___x_335_, v_a_331_, v___x_307_, v___x_308_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_336_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
v___jp_310_:
{
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___y_311_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed(lean_object* v_action_341_, lean_object* v_a_342_, lean_object* v___f_343_, lean_object* v___f_344_, lean_object* v_x_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(v_action_341_, v_a_342_, v___f_343_, v___f_344_, v_x_345_);
lean_dec_ref(v_a_342_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(lean_object* v_s_357_, uint8_t v_releaseConnectionPermit_358_, lean_object* v_action_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; lean_object* v_context_363_; lean_object* v_activeConnections_364_; lean_object* v_connectionLimit_365_; lean_object* v_shutdownPromise_366_; lean_object* v___f_367_; lean_object* v___f_368_; lean_object* v___f_369_; lean_object* v___x_1520__overap_370_; lean_object* v___x_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; 
v___x_362_ = l_Std_Async_ContextAsync_instMonad;
v_context_363_ = lean_ctor_get(v_s_357_, 0);
lean_inc_ref(v_context_363_);
v_activeConnections_364_ = lean_ctor_get(v_s_357_, 1);
lean_inc_ref_n(v_activeConnections_364_, 2);
v_connectionLimit_365_ = lean_ctor_get(v_s_357_, 2);
lean_inc(v_connectionLimit_365_);
v_shutdownPromise_366_ = lean_ctor_get(v_s_357_, 3);
lean_inc_ref(v_shutdownPromise_366_);
lean_dec_ref(v_s_357_);
v___f_367_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_368_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_369_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
v___x_1520__overap_370_ = l_Std_Mutex_atomically___redArg(v___x_362_, v___f_368_, v___f_369_, v_activeConnections_364_, v___f_367_);
lean_inc_ref_n(v_a_360_, 4);
v___x_371_ = lean_apply_2(v___x_1520__overap_370_, v_a_360_, lean_box(0));
v___f_372_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_373_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_373_, 0, v_context_363_);
lean_closure_set(v___f_373_, 1, v_shutdownPromise_366_);
v___f_374_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_374_, 0, v___f_373_);
v___f_375_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_376_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_376_, 0, v___x_362_);
lean_closure_set(v___f_376_, 1, v___f_372_);
lean_closure_set(v___f_376_, 2, v___f_374_);
lean_closure_set(v___f_376_, 3, v___f_368_);
lean_closure_set(v___f_376_, 4, v___f_369_);
lean_closure_set(v___f_376_, 5, v_activeConnections_364_);
lean_inc_ref(v___f_376_);
v___f_377_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_377_, 0, v___f_376_);
lean_closure_set(v___f_377_, 1, v_a_360_);
v___x_378_ = lean_box(v_releaseConnectionPermit_358_);
v___f_379_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_379_, 0, v___x_378_);
lean_closure_set(v___f_379_, 1, v___f_376_);
lean_closure_set(v___f_379_, 2, v_a_360_);
lean_closure_set(v___f_379_, 3, v_connectionLimit_365_);
lean_closure_set(v___f_379_, 4, v___f_377_);
v___f_380_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_380_, 0, v_action_359_);
lean_closure_set(v___f_380_, 1, v_a_360_);
lean_closure_set(v___f_380_, 2, v___f_379_);
lean_closure_set(v___f_380_, 3, v___f_375_);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = 0;
v___x_383_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_381_, v___x_382_, v___x_371_, v___f_380_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(lean_object* v_s_384_, lean_object* v_releaseConnectionPermit_385_, lean_object* v_action_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_389_; lean_object* v_res_390_; 
v_releaseConnectionPermit_boxed_389_ = lean_unbox(v_releaseConnectionPermit_385_);
v_res_390_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(v_s_384_, v_releaseConnectionPermit_boxed_389_, v_action_386_, v_a_387_);
lean_dec_ref(v_a_387_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(lean_object* v_00_u03b1_391_, lean_object* v_s_392_, uint8_t v_releaseConnectionPermit_393_, lean_object* v_action_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; lean_object* v_context_398_; lean_object* v_activeConnections_399_; lean_object* v_connectionLimit_400_; lean_object* v_shutdownPromise_401_; lean_object* v___f_402_; lean_object* v___f_403_; lean_object* v___f_404_; lean_object* v___x_2130__overap_405_; lean_object* v___x_406_; lean_object* v___f_407_; lean_object* v___f_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___f_414_; lean_object* v___f_415_; lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; 
v___x_397_ = l_Std_Async_ContextAsync_instMonad;
v_context_398_ = lean_ctor_get(v_s_392_, 0);
lean_inc_ref(v_context_398_);
v_activeConnections_399_ = lean_ctor_get(v_s_392_, 1);
lean_inc_ref_n(v_activeConnections_399_, 2);
v_connectionLimit_400_ = lean_ctor_get(v_s_392_, 2);
lean_inc(v_connectionLimit_400_);
v_shutdownPromise_401_ = lean_ctor_get(v_s_392_, 3);
lean_inc_ref(v_shutdownPromise_401_);
lean_dec_ref(v_s_392_);
v___f_402_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_403_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_404_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
v___x_2130__overap_405_ = l_Std_Mutex_atomically___redArg(v___x_397_, v___f_403_, v___f_404_, v_activeConnections_399_, v___f_402_);
lean_inc_ref_n(v_a_395_, 4);
v___x_406_ = lean_apply_2(v___x_2130__overap_405_, v_a_395_, lean_box(0));
v___f_407_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_408_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_408_, 0, v_context_398_);
lean_closure_set(v___f_408_, 1, v_shutdownPromise_401_);
v___f_409_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_409_, 0, v___f_408_);
v___f_410_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6));
v___f_411_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_411_, 0, v___x_397_);
lean_closure_set(v___f_411_, 1, v___f_407_);
lean_closure_set(v___f_411_, 2, v___f_409_);
lean_closure_set(v___f_411_, 3, v___f_403_);
lean_closure_set(v___f_411_, 4, v___f_404_);
lean_closure_set(v___f_411_, 5, v_activeConnections_399_);
lean_inc_ref(v___f_411_);
v___f_412_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_412_, 0, v___f_411_);
lean_closure_set(v___f_412_, 1, v_a_395_);
v___x_413_ = lean_box(v_releaseConnectionPermit_393_);
v___f_414_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_414_, 0, v___x_413_);
lean_closure_set(v___f_414_, 1, v___f_411_);
lean_closure_set(v___f_414_, 2, v_a_395_);
lean_closure_set(v___f_414_, 3, v_connectionLimit_400_);
lean_closure_set(v___f_414_, 4, v___f_412_);
v___f_415_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_415_, 0, v_action_394_);
lean_closure_set(v___f_415_, 1, v_a_395_);
lean_closure_set(v___f_415_, 2, v___f_414_);
lean_closure_set(v___f_415_, 3, v___f_410_);
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = 0;
v___x_418_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_416_, v___x_417_, v___x_406_, v___f_415_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(lean_object* v_00_u03b1_419_, lean_object* v_s_420_, lean_object* v_releaseConnectionPermit_421_, lean_object* v_action_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
uint8_t v_releaseConnectionPermit_boxed_425_; lean_object* v_res_426_; 
v_releaseConnectionPermit_boxed_425_ = lean_unbox(v_releaseConnectionPermit_421_);
v_res_426_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(v_00_u03b1_419_, v_s_420_, v_releaseConnectionPermit_boxed_425_, v_action_422_, v_a_423_);
lean_dec_ref(v_a_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0(lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_x_427_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; 
lean_dec_ref(v_x_427_);
v___x_430_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__0___boxed(lean_object* v_x_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_Http_Server_serve___redArg___lam__0(v_x_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1(lean_object* v_x_434_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_444_; 
v_a_436_ = lean_ctor_get(v_x_434_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_444_ == 0)
{
v___x_438_ = v_x_434_;
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v_x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_443_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; 
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_473_; 
v_a_445_ = lean_ctor_get(v_x_434_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_473_ == 0)
{
v___x_447_ = v_x_434_;
v_isShared_448_ = v_isSharedCheck_473_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v_x_434_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_473_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
if (lean_obj_tag(v_a_445_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_460_; 
v_a_449_ = lean_ctor_get(v_a_445_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v_a_445_);
if (v_isSharedCheck_460_ == 0)
{
v___x_451_ = v_a_445_;
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v_a_445_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set_tag(v___x_451_, 1);
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_459_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_456_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_454_);
v___x_456_ = v___x_447_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_458_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_472_; 
v_a_461_ = lean_ctor_get(v_a_445_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_a_445_);
if (v_isSharedCheck_472_ == 0)
{
v___x_463_ = v_a_445_;
v_isShared_464_ = v_isSharedCheck_472_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v_a_445_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_472_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set_tag(v___x_463_, 0);
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_471_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_466_);
v___x_468_ = v___x_447_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_470_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; 
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__1___boxed(lean_object* v_x_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3(lean_object* v_x_477_){
_start:
{
lean_object* v_fst_478_; 
v_fst_478_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_fst_478_);
return v_fst_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__3___boxed(lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_479_);
lean_dec_ref(v_x_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4(lean_object* v_x_485_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__4___closed__1));
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__4___boxed(lean_object* v_x_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2(lean_object* v_x_491_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v_x_491_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__2___boxed(lean_object* v_x_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5(lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_499_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_509_; 
v_a_501_ = lean_ctor_get(v_x_499_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_509_ == 0)
{
v___x_503_ = v_x_499_;
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v_x_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_508_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_520_; 
v_a_510_ = lean_ctor_get(v_x_499_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_520_ == 0)
{
v___x_512_ = v_x_499_;
v_isShared_513_ = v_isSharedCheck_520_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v_x_499_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_520_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_token_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v_token_514_ = lean_ctor_get(v_a_510_, 1);
lean_inc_ref(v_token_514_);
lean_dec(v_a_510_);
v___x_515_ = l_Std_CancellationToken_selector(v_token_514_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_515_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_519_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; 
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__5___boxed(lean_object* v_x_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_Http_Server_serve___redArg___lam__5(v_x_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7(lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
if (lean_obj_tag(v_x_525_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_535_; 
lean_dec_ref(v_x_524_);
v_a_527_ = lean_ctor_get(v_x_525_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v_x_525_);
if (v_isSharedCheck_535_ == 0)
{
v___x_529_ = v_x_525_;
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v_x_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_534_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; 
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
}
else
{
lean_object* v___x_536_; 
lean_dec_ref(v_x_525_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v_x_524_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__7___boxed(lean_object* v_x_537_, lean_object* v_x_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_Http_Server_serve___redArg___lam__7(v_x_537_, v_x_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8(lean_object* v_a_541_, lean_object* v_x_542_){
_start:
{
if (lean_obj_tag(v_x_542_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_a_541_);
v_a_544_ = lean_ctor_get(v_x_542_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_542_);
if (v_isSharedCheck_552_ == 0)
{
v___x_546_ = v_x_542_;
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v_x_542_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_551_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
}
else
{
lean_object* v_context_553_; lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_570_; 
v_context_553_ = lean_ctor_get(v_a_541_, 0);
lean_inc_ref(v_context_553_);
v_a_554_ = lean_ctor_get(v_x_542_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v_x_542_);
if (v_isSharedCheck_570_ == 0)
{
v___x_556_ = v_x_542_;
v_isShared_557_ = v_isSharedCheck_570_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v_x_542_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_570_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v_shutdownPromise_558_; lean_object* v_token_559_; uint8_t v___x_560_; lean_object* v___f_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v_shutdownPromise_558_ = lean_ctor_get(v_a_541_, 3);
lean_inc_ref(v_shutdownPromise_558_);
lean_dec_ref(v_a_541_);
v_token_559_ = lean_ctor_get(v_context_553_, 1);
lean_inc_ref(v_token_559_);
lean_dec_ref(v_context_553_);
v___x_560_ = l_Std_CancellationToken_isCancelled(v_token_559_);
v___f_561_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_561_, 0, v_a_554_);
lean_closure_set(v___f_561_, 1, v_shutdownPromise_558_);
v___x_562_ = lean_box(v___x_560_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_562_);
v___x_564_ = v___x_556_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_569_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; 
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = 0;
v___x_568_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_566_, v___x_567_, v___x_565_, v___f_561_);
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__8___boxed(lean_object* v_a_571_, lean_object* v_x_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_Http_Server_serve___redArg___lam__8(v_a_571_, v_x_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9(lean_object* v___x_575_, lean_object* v_____r_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_575_);
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__9___boxed(lean_object* v___x_582_, lean_object* v_____r_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_Http_Server_serve___redArg___lam__9(v___x_582_, v_____r_583_, v___y_584_);
lean_dec_ref(v___y_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6(lean_object* v___x_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_588_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
v_a_590_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_598_ == 0)
{
v___x_592_ = v_x_588_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v_x_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
}
else
{
lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_607_; 
v_isSharedCheck_607_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v_x_588_, 0);
lean_dec(v_unused_608_);
v___x_600_ = v_x_588_;
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
else
{
lean_dec(v_x_588_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_587_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_602_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_606_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__6___boxed(lean_object* v___x_609_, lean_object* v_x_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_Http_Server_serve___redArg___lam__6(v___x_609_, v_x_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10(lean_object* v___f_613_, lean_object* v___y_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v___f_613_);
v_a_617_ = lean_ctor_get(v_x_615_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_625_ == 0)
{
v___x_619_ = v_x_615_;
v_isShared_620_ = v_isSharedCheck_625_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v_x_615_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_625_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_624_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; 
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_627_; 
v_a_626_ = lean_ctor_get(v_x_615_, 0);
lean_inc(v_a_626_);
lean_dec_ref(v_x_615_);
lean_inc_ref(v___y_614_);
v___x_627_ = lean_apply_3(v___f_613_, v_a_626_, v___y_614_, lean_box(0));
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__10___boxed(lean_object* v___f_628_, lean_object* v___y_629_, lean_object* v_x_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_Http_Server_serve___redArg___lam__10(v___f_628_, v___y_629_, v_x_630_);
lean_dec_ref(v___y_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11(lean_object* v_a_633_, lean_object* v_x_634_){
_start:
{
if (lean_obj_tag(v_x_634_) == 0)
{
lean_object* v___x_636_; 
lean_dec_ref(v_a_633_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_x_634_);
return v___x_636_;
}
else
{
lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_646_; 
v_isSharedCheck_646_ = !lean_is_exclusive(v_x_634_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; 
v_unused_647_ = lean_ctor_get(v_x_634_, 0);
lean_dec(v_unused_647_);
v___x_638_ = v_x_634_;
v_isShared_639_ = v_isSharedCheck_646_;
goto v_resetjp_637_;
}
else
{
lean_dec(v_x_634_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_646_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_640_ = lean_box(2);
v___x_641_ = l_Std_CancellationContext_cancel(v_a_633_, v___x_640_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_645_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; 
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__11___boxed(lean_object* v_a_648_, lean_object* v_x_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Http_Server_serve___redArg___lam__11(v_a_648_, v_x_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13(lean_object* v___f_652_, lean_object* v_a_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v___x_656_; 
lean_dec_ref(v_a_653_);
lean_dec_ref(v___f_652_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_x_654_);
return v___x_656_;
}
else
{
lean_object* v_a_657_; lean_object* v___x_658_; 
v_a_657_ = lean_ctor_get(v_x_654_, 0);
lean_inc(v_a_657_);
lean_dec_ref(v_x_654_);
v___x_658_ = lean_apply_3(v___f_652_, v_a_657_, v_a_653_, lean_box(0));
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__13___boxed(lean_object* v___f_659_, lean_object* v_a_660_, lean_object* v_x_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_Http_Server_serve___redArg___lam__13(v___f_659_, v_a_660_, v_x_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12(uint8_t v_permitAcquired_664_, lean_object* v___f_665_, lean_object* v___x_666_, lean_object* v_a_667_, lean_object* v_connectionLimit_668_, lean_object* v___x_669_, uint8_t v___x_670_, lean_object* v___f_671_, lean_object* v_opt_672_){
_start:
{
if (v_permitAcquired_664_ == 0)
{
lean_object* v___x_674_; 
lean_dec_ref(v___f_671_);
lean_dec(v___x_669_);
lean_dec(v_connectionLimit_668_);
v___x_674_ = lean_apply_3(v___f_665_, v___x_666_, v_a_667_, lean_box(0));
return v___x_674_;
}
else
{
if (lean_obj_tag(v_connectionLimit_668_) == 1)
{
lean_object* v_val_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v_a_667_);
lean_dec_ref(v___f_665_);
v_val_675_ = lean_ctor_get(v_connectionLimit_668_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v_connectionLimit_668_);
if (v_isSharedCheck_685_ == 0)
{
v___x_677_ = v_connectionLimit_668_;
v_isShared_678_ = v_isSharedCheck_685_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_val_675_);
lean_dec(v_connectionLimit_668_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_685_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = l_Std_Semaphore_release(v_val_675_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_679_);
v___x_681_ = v___x_677_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_684_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
v___x_683_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_669_, v___x_670_, v___x_682_, v___f_671_);
return v___x_683_;
}
}
}
else
{
lean_object* v___x_686_; 
lean_dec_ref(v___f_671_);
lean_dec(v___x_669_);
lean_dec(v_connectionLimit_668_);
v___x_686_ = lean_apply_3(v___f_665_, v___x_666_, v_a_667_, lean_box(0));
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__12___boxed(lean_object* v_permitAcquired_687_, lean_object* v___f_688_, lean_object* v___x_689_, lean_object* v_a_690_, lean_object* v_connectionLimit_691_, lean_object* v___x_692_, lean_object* v___x_693_, lean_object* v___f_694_, lean_object* v_opt_695_, lean_object* v___y_696_){
_start:
{
uint8_t v_permitAcquired_boxed_697_; uint8_t v___x_13082__boxed_698_; lean_object* v_res_699_; 
v_permitAcquired_boxed_697_ = lean_unbox(v_permitAcquired_687_);
v___x_13082__boxed_698_ = lean_unbox(v___x_693_);
v_res_699_ = l_Std_Http_Server_serve___redArg___lam__12(v_permitAcquired_boxed_697_, v___f_688_, v___x_689_, v_a_690_, v_connectionLimit_691_, v___x_692_, v___x_13082__boxed_698_, v___f_694_, v_opt_695_);
lean_dec(v_opt_695_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14(lean_object* v___x_700_, lean_object* v_inst_701_, lean_object* v_val_702_, lean_object* v_handler_703_, lean_object* v_config_704_, lean_object* v_extensions_705_, lean_object* v_a_706_, lean_object* v___f_707_, lean_object* v___x_708_, uint8_t v___x_709_, lean_object* v___f_710_, lean_object* v_x_711_){
_start:
{
if (lean_obj_tag(v_x_711_) == 0)
{
lean_object* v___x_713_; 
lean_dec_ref(v___f_710_);
lean_dec(v___x_708_);
lean_dec_ref(v___f_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_extensions_705_);
lean_dec_ref(v_config_704_);
lean_dec(v_handler_703_);
lean_dec(v_val_702_);
lean_dec_ref(v_inst_701_);
lean_dec_ref(v___x_700_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v_x_711_);
return v___x_713_;
}
else
{
lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_752_; 
v_isSharedCheck_752_ = !lean_is_exclusive(v_x_711_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v_x_711_, 0);
lean_dec(v_unused_753_);
v___x_715_ = v_x_711_;
v_isShared_716_ = v_isSharedCheck_752_;
goto v_resetjp_714_;
}
else
{
lean_dec(v_x_711_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_752_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___y_720_; 
v___x_717_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___boxed), 10, 9);
lean_closure_set(v___x_717_, 0, lean_box(0));
lean_closure_set(v___x_717_, 1, lean_box(0));
lean_closure_set(v___x_717_, 2, v___x_700_);
lean_closure_set(v___x_717_, 3, v_inst_701_);
lean_closure_set(v___x_717_, 4, v_val_702_);
lean_closure_set(v___x_717_, 5, v_handler_703_);
lean_closure_set(v___x_717_, 6, v_config_704_);
lean_closure_set(v___x_717_, 7, v_extensions_705_);
lean_closure_set(v___x_717_, 8, v_a_706_);
lean_inc(v___x_708_);
v___x_718_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_717_, v___f_707_, v___x_708_, v___x_709_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_724_; 
lean_dec_ref(v___f_710_);
lean_dec(v___x_708_);
v_a_724_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_718_);
if (lean_obj_tag(v_a_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_725_ = lean_ctor_get(v_a_724_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_a_724_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v_a_724_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v_a_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
v___y_720_ = v___x_730_;
goto v___jp_719_;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_741_; 
v_a_733_ = lean_ctor_get(v_a_724_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_a_724_);
if (v_isSharedCheck_741_ == 0)
{
v___x_735_ = v_a_724_;
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v_a_724_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_fst_737_; lean_object* v___x_739_; 
v_fst_737_ = lean_ctor_get(v_a_733_, 0);
lean_inc(v_fst_737_);
lean_dec(v_a_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v_fst_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_fst_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
v___y_720_ = v___x_739_;
goto v___jp_719_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_751_; 
lean_del_object(v___x_715_);
v_a_742_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_751_ == 0)
{
v___x_744_ = v___x_718_;
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_718_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_746_, 0, lean_box(0));
lean_closure_set(v___x_746_, 1, lean_box(0));
lean_closure_set(v___x_746_, 2, lean_box(0));
lean_closure_set(v___x_746_, 3, v___f_710_);
v___x_747_ = lean_task_map(v___x_746_, v_a_742_, v___x_708_, v___x_709_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_747_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
v___jp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 0);
lean_ctor_set(v___x_715_, 0, v___y_720_);
v___x_722_ = v___x_715_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___y_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__14___boxed(lean_object* v___x_754_, lean_object* v_inst_755_, lean_object* v_val_756_, lean_object* v_handler_757_, lean_object* v_config_758_, lean_object* v_extensions_759_, lean_object* v_a_760_, lean_object* v___f_761_, lean_object* v___x_762_, lean_object* v___x_763_, lean_object* v___f_764_, lean_object* v_x_765_, lean_object* v___y_766_){
_start:
{
uint8_t v___x_13131__boxed_767_; lean_object* v_res_768_; 
v___x_13131__boxed_767_ = lean_unbox(v___x_763_);
v_res_768_ = l_Std_Http_Server_serve___redArg___lam__14(v___x_754_, v_inst_755_, v_val_756_, v_handler_757_, v_config_758_, v_extensions_759_, v_a_760_, v___f_761_, v___x_762_, v___x_13131__boxed_767_, v___f_764_, v_x_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15(lean_object* v___x_769_, lean_object* v_activeConnections_770_, lean_object* v___f_771_, lean_object* v_a_772_, lean_object* v___f_773_, lean_object* v___f_774_, uint8_t v_permitAcquired_775_, lean_object* v___x_776_, lean_object* v_connectionLimit_777_, lean_object* v___x_778_, uint8_t v___x_779_, lean_object* v___x_780_, lean_object* v_inst_781_, lean_object* v_val_782_, lean_object* v_handler_783_, lean_object* v_config_784_, lean_object* v_extensions_785_, lean_object* v___f_786_, lean_object* v___f_787_){
_start:
{
lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___x_12194__overap_791_; lean_object* v___x_792_; lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___f_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___f_789_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3));
v___f_790_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4));
lean_inc_ref(v_activeConnections_770_);
lean_inc_ref(v___x_769_);
v___x_12194__overap_791_ = l_Std_Mutex_atomically___redArg(v___x_769_, v___f_789_, v___f_790_, v_activeConnections_770_, v___f_771_);
lean_inc_ref_n(v_a_772_, 3);
v___x_792_ = lean_apply_2(v___x_12194__overap_791_, v_a_772_, lean_box(0));
v___f_793_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_793_, 0, v___x_769_);
lean_closure_set(v___f_793_, 1, v___f_773_);
lean_closure_set(v___f_793_, 2, v___f_774_);
lean_closure_set(v___f_793_, 3, v___f_789_);
lean_closure_set(v___f_793_, 4, v___f_790_);
lean_closure_set(v___f_793_, 5, v_activeConnections_770_);
lean_inc_ref(v___f_793_);
v___f_794_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__13___boxed), 4, 2);
lean_closure_set(v___f_794_, 0, v___f_793_);
lean_closure_set(v___f_794_, 1, v_a_772_);
v___x_795_ = lean_box(v_permitAcquired_775_);
v___x_796_ = lean_box(v___x_779_);
lean_inc_n(v___x_778_, 3);
v___f_797_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__12___boxed), 10, 8);
lean_closure_set(v___f_797_, 0, v___x_795_);
lean_closure_set(v___f_797_, 1, v___f_793_);
lean_closure_set(v___f_797_, 2, v___x_776_);
lean_closure_set(v___f_797_, 3, v_a_772_);
lean_closure_set(v___f_797_, 4, v_connectionLimit_777_);
lean_closure_set(v___f_797_, 5, v___x_778_);
lean_closure_set(v___f_797_, 6, v___x_796_);
lean_closure_set(v___f_797_, 7, v___f_794_);
v___x_798_ = lean_box(v___x_779_);
v___f_799_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__14___boxed), 13, 11);
lean_closure_set(v___f_799_, 0, v___x_780_);
lean_closure_set(v___f_799_, 1, v_inst_781_);
lean_closure_set(v___f_799_, 2, v_val_782_);
lean_closure_set(v___f_799_, 3, v_handler_783_);
lean_closure_set(v___f_799_, 4, v_config_784_);
lean_closure_set(v___f_799_, 5, v_extensions_785_);
lean_closure_set(v___f_799_, 6, v_a_772_);
lean_closure_set(v___f_799_, 7, v___f_797_);
lean_closure_set(v___f_799_, 8, v___x_778_);
lean_closure_set(v___f_799_, 9, v___x_798_);
lean_closure_set(v___f_799_, 10, v___f_786_);
v___x_800_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_778_, v___x_779_, v___x_792_, v___f_799_);
v___x_801_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_778_, v___x_779_, v___x_800_, v___f_787_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__15___boxed(lean_object** _args){
lean_object* v___x_802_ = _args[0];
lean_object* v_activeConnections_803_ = _args[1];
lean_object* v___f_804_ = _args[2];
lean_object* v_a_805_ = _args[3];
lean_object* v___f_806_ = _args[4];
lean_object* v___f_807_ = _args[5];
lean_object* v_permitAcquired_808_ = _args[6];
lean_object* v___x_809_ = _args[7];
lean_object* v_connectionLimit_810_ = _args[8];
lean_object* v___x_811_ = _args[9];
lean_object* v___x_812_ = _args[10];
lean_object* v___x_813_ = _args[11];
lean_object* v_inst_814_ = _args[12];
lean_object* v_val_815_ = _args[13];
lean_object* v_handler_816_ = _args[14];
lean_object* v_config_817_ = _args[15];
lean_object* v_extensions_818_ = _args[16];
lean_object* v___f_819_ = _args[17];
lean_object* v___f_820_ = _args[18];
lean_object* v___y_821_ = _args[19];
_start:
{
uint8_t v_permitAcquired_boxed_822_; uint8_t v___x_13250__boxed_823_; lean_object* v_res_824_; 
v_permitAcquired_boxed_822_ = lean_unbox(v_permitAcquired_808_);
v___x_13250__boxed_823_ = lean_unbox(v___x_812_);
v_res_824_ = l_Std_Http_Server_serve___redArg___lam__15(v___x_802_, v_activeConnections_803_, v___f_804_, v_a_805_, v___f_806_, v___f_807_, v_permitAcquired_boxed_822_, v___x_809_, v_connectionLimit_810_, v___x_811_, v___x_13250__boxed_823_, v___x_813_, v_inst_814_, v_val_815_, v_handler_816_, v_config_817_, v_extensions_818_, v___f_819_, v___f_820_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16(lean_object* v___x_825_, lean_object* v_activeConnections_826_, lean_object* v___f_827_, lean_object* v___f_828_, lean_object* v___f_829_, uint8_t v_permitAcquired_830_, lean_object* v___x_831_, lean_object* v_connectionLimit_832_, lean_object* v___x_833_, uint8_t v___x_834_, lean_object* v___x_835_, lean_object* v_inst_836_, lean_object* v_val_837_, lean_object* v_handler_838_, lean_object* v_config_839_, lean_object* v_extensions_840_, lean_object* v___f_841_, lean_object* v_x_842_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_852_; 
lean_dec_ref(v___f_841_);
lean_dec(v_extensions_840_);
lean_dec_ref(v_config_839_);
lean_dec(v_handler_838_);
lean_dec(v_val_837_);
lean_dec_ref(v_inst_836_);
lean_dec_ref(v___x_835_);
lean_dec(v___x_833_);
lean_dec(v_connectionLimit_832_);
lean_dec_ref(v___f_829_);
lean_dec_ref(v___f_828_);
lean_dec_ref(v___f_827_);
lean_dec_ref(v_activeConnections_826_);
lean_dec_ref(v___x_825_);
v_a_844_ = lean_ctor_get(v_x_842_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_852_ == 0)
{
v___x_846_ = v_x_842_;
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v_x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_851_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; 
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_867_; 
v_a_853_ = lean_ctor_get(v_x_842_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_867_ == 0)
{
v___x_855_ = v_x_842_;
v_isShared_856_ = v_isSharedCheck_867_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v_x_842_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_867_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
lean_inc(v_a_853_);
v___f_857_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_857_, 0, v_a_853_);
v___x_858_ = lean_box(v_permitAcquired_830_);
v___x_859_ = lean_box(v___x_834_);
lean_inc(v___x_833_);
v___f_860_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__15___boxed), 20, 19);
lean_closure_set(v___f_860_, 0, v___x_825_);
lean_closure_set(v___f_860_, 1, v_activeConnections_826_);
lean_closure_set(v___f_860_, 2, v___f_827_);
lean_closure_set(v___f_860_, 3, v_a_853_);
lean_closure_set(v___f_860_, 4, v___f_828_);
lean_closure_set(v___f_860_, 5, v___f_829_);
lean_closure_set(v___f_860_, 6, v___x_858_);
lean_closure_set(v___f_860_, 7, v___x_831_);
lean_closure_set(v___f_860_, 8, v_connectionLimit_832_);
lean_closure_set(v___f_860_, 9, v___x_833_);
lean_closure_set(v___f_860_, 10, v___x_859_);
lean_closure_set(v___f_860_, 11, v___x_835_);
lean_closure_set(v___f_860_, 12, v_inst_836_);
lean_closure_set(v___f_860_, 13, v_val_837_);
lean_closure_set(v___f_860_, 14, v_handler_838_);
lean_closure_set(v___f_860_, 15, v_config_839_);
lean_closure_set(v___f_860_, 16, v_extensions_840_);
lean_closure_set(v___f_860_, 17, v___f_841_);
lean_closure_set(v___f_860_, 18, v___f_857_);
v___x_861_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_861_, 0, lean_box(0));
lean_closure_set(v___x_861_, 1, v___f_860_);
v___x_862_ = lean_io_as_task(v___x_861_, v___x_833_);
lean_dec_ref(v___x_862_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_831_);
v___x_864_ = v___x_855_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_831_);
v___x_864_ = v_reuseFailAlloc_866_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; 
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__16___boxed(lean_object** _args){
lean_object* v___x_868_ = _args[0];
lean_object* v_activeConnections_869_ = _args[1];
lean_object* v___f_870_ = _args[2];
lean_object* v___f_871_ = _args[3];
lean_object* v___f_872_ = _args[4];
lean_object* v_permitAcquired_873_ = _args[5];
lean_object* v___x_874_ = _args[6];
lean_object* v_connectionLimit_875_ = _args[7];
lean_object* v___x_876_ = _args[8];
lean_object* v___x_877_ = _args[9];
lean_object* v___x_878_ = _args[10];
lean_object* v_inst_879_ = _args[11];
lean_object* v_val_880_ = _args[12];
lean_object* v_handler_881_ = _args[13];
lean_object* v_config_882_ = _args[14];
lean_object* v_extensions_883_ = _args[15];
lean_object* v___f_884_ = _args[16];
lean_object* v_x_885_ = _args[17];
lean_object* v___y_886_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_887_; uint8_t v___x_13317__boxed_888_; lean_object* v_res_889_; 
v_permitAcquired_boxed_887_ = lean_unbox(v_permitAcquired_873_);
v___x_13317__boxed_888_ = lean_unbox(v___x_877_);
v_res_889_ = l_Std_Http_Server_serve___redArg___lam__16(v___x_868_, v_activeConnections_869_, v___f_870_, v___f_871_, v___f_872_, v_permitAcquired_boxed_887_, v___x_874_, v_connectionLimit_875_, v___x_876_, v___x_13317__boxed_888_, v___x_878_, v_inst_879_, v_val_880_, v_handler_881_, v_config_882_, v_extensions_883_, v___f_884_, v_x_885_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17(lean_object* v___x_890_, uint8_t v___x_891_, lean_object* v___f_892_, lean_object* v_x_893_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v___f_892_);
lean_dec(v___x_890_);
v_a_895_ = lean_ctor_get(v_x_893_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_903_ == 0)
{
v___x_897_ = v_x_893_;
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v_x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_902_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_914_; 
v_a_904_ = lean_ctor_get(v_x_893_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_914_ == 0)
{
v___x_906_ = v_x_893_;
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v_x_893_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = l_Std_CancellationContext_fork(v_a_904_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_908_);
v___x_910_ = v___x_906_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_913_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
v___x_912_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_890_, v___x_891_, v___x_911_, v___f_892_);
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__17___boxed(lean_object* v___x_915_, lean_object* v___x_916_, lean_object* v___f_917_, lean_object* v_x_918_, lean_object* v___y_919_){
_start:
{
uint8_t v___x_13399__boxed_920_; lean_object* v_res_921_; 
v___x_13399__boxed_920_ = lean_unbox(v___x_916_);
v_res_921_ = l_Std_Http_Server_serve___redArg___lam__17(v___x_915_, v___x_13399__boxed_920_, v___f_917_, v_x_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18(lean_object* v___x_922_, lean_object* v_activeConnections_923_, lean_object* v___f_924_, lean_object* v___f_925_, lean_object* v___f_926_, uint8_t v_permitAcquired_927_, lean_object* v___x_928_, lean_object* v_connectionLimit_929_, uint8_t v___x_930_, lean_object* v_inst_931_, lean_object* v_val_932_, lean_object* v_handler_933_, lean_object* v_config_934_, lean_object* v___f_935_, lean_object* v___f_936_, lean_object* v_extensions_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___f_944_; lean_object* v___x_945_; lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_940_ = l_Std_Http_instTransportClient;
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_box(v_permitAcquired_927_);
v___x_943_ = lean_box(v___x_930_);
v___f_944_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__16___boxed), 19, 17);
lean_closure_set(v___f_944_, 0, v___x_922_);
lean_closure_set(v___f_944_, 1, v_activeConnections_923_);
lean_closure_set(v___f_944_, 2, v___f_924_);
lean_closure_set(v___f_944_, 3, v___f_925_);
lean_closure_set(v___f_944_, 4, v___f_926_);
lean_closure_set(v___f_944_, 5, v___x_942_);
lean_closure_set(v___f_944_, 6, v___x_928_);
lean_closure_set(v___f_944_, 7, v_connectionLimit_929_);
lean_closure_set(v___f_944_, 8, v___x_941_);
lean_closure_set(v___f_944_, 9, v___x_943_);
lean_closure_set(v___f_944_, 10, v___x_940_);
lean_closure_set(v___f_944_, 11, v_inst_931_);
lean_closure_set(v___f_944_, 12, v_val_932_);
lean_closure_set(v___f_944_, 13, v_handler_933_);
lean_closure_set(v___f_944_, 14, v_config_934_);
lean_closure_set(v___f_944_, 15, v_extensions_937_);
lean_closure_set(v___f_944_, 16, v___f_935_);
v___x_945_ = lean_box(v___x_930_);
v___f_946_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__17___boxed), 5, 3);
lean_closure_set(v___f_946_, 0, v___x_941_);
lean_closure_set(v___f_946_, 1, v___x_945_);
lean_closure_set(v___f_946_, 2, v___f_944_);
lean_inc_ref(v___y_938_);
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v___y_938_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
v___x_949_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_941_, v___x_930_, v___x_948_, v___f_946_);
v___x_950_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_941_, v___x_930_, v___x_949_, v___f_936_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__18___boxed(lean_object** _args){
lean_object* v___x_951_ = _args[0];
lean_object* v_activeConnections_952_ = _args[1];
lean_object* v___f_953_ = _args[2];
lean_object* v___f_954_ = _args[3];
lean_object* v___f_955_ = _args[4];
lean_object* v_permitAcquired_956_ = _args[5];
lean_object* v___x_957_ = _args[6];
lean_object* v_connectionLimit_958_ = _args[7];
lean_object* v___x_959_ = _args[8];
lean_object* v_inst_960_ = _args[9];
lean_object* v_val_961_ = _args[10];
lean_object* v_handler_962_ = _args[11];
lean_object* v_config_963_ = _args[12];
lean_object* v___f_964_ = _args[13];
lean_object* v___f_965_ = _args[14];
lean_object* v_extensions_966_ = _args[15];
lean_object* v___y_967_ = _args[16];
lean_object* v___y_968_ = _args[17];
_start:
{
uint8_t v_permitAcquired_boxed_969_; uint8_t v___x_13458__boxed_970_; lean_object* v_res_971_; 
v_permitAcquired_boxed_969_ = lean_unbox(v_permitAcquired_956_);
v___x_13458__boxed_970_ = lean_unbox(v___x_959_);
v_res_971_ = l_Std_Http_Server_serve___redArg___lam__18(v___x_951_, v_activeConnections_952_, v___f_953_, v___f_954_, v___f_955_, v_permitAcquired_boxed_969_, v___x_957_, v_connectionLimit_958_, v___x_13458__boxed_970_, v_inst_960_, v_val_961_, v_handler_962_, v_config_963_, v___f_964_, v___f_965_, v_extensions_966_, v___y_967_);
lean_dec_ref(v___y_967_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19(lean_object* v___f_972_, lean_object* v___y_973_, lean_object* v_x_974_){
_start:
{
if (lean_obj_tag(v_x_974_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_984_; 
lean_dec_ref(v___f_972_);
v_a_976_ = lean_ctor_get(v_x_974_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v_x_974_);
if (v_isSharedCheck_984_ == 0)
{
v___x_978_ = v_x_974_;
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v_x_974_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_983_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; 
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_986_; 
v_a_985_ = lean_ctor_get(v_x_974_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v_x_974_);
lean_inc_ref(v___y_973_);
v___x_986_ = lean_apply_3(v___f_972_, v_a_985_, v___y_973_, lean_box(0));
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__19___boxed(lean_object* v___f_987_, lean_object* v___y_988_, lean_object* v_x_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Std_Http_Server_serve___redArg___lam__19(v___f_987_, v___y_988_, v_x_989_);
lean_dec_ref(v___y_988_);
return v_res_991_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__21___closed__0(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = l_Std_Http_Extensions_empty;
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Std_Http_Server_serve___redArg___lam__21___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__21___closed__0, &l_Std_Http_Server_serve___redArg___lam__21___closed__0_once, _init_l_Std_Http_Server_serve___redArg___lam__21___closed__0);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21(uint8_t v___x_997_, lean_object* v___f_998_, lean_object* v___f_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v___f_999_);
lean_dec_ref(v___f_998_);
v_a_1002_ = lean_ctor_get(v_x_1000_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1004_ = v_x_1000_;
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v_x_1000_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
}
else
{
lean_object* v_a_1011_; 
v_a_1011_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v_x_1000_);
if (lean_obj_tag(v_a_1011_) == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec_ref(v_a_1011_);
lean_dec_ref(v___f_999_);
v___x_1012_ = lean_obj_once(&l_Std_Http_Server_serve___redArg___lam__21___closed__1, &l_Std_Http_Server_serve___redArg___lam__21___closed__1_once, _init_l_Std_Http_Server_serve___redArg___lam__21___closed__1);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1013_, v___x_997_, v___x_1012_, v___f_998_);
return v___x_1014_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v___f_998_);
v_a_1015_ = lean_ctor_get(v_a_1011_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_a_1011_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1017_ = v_a_1011_;
v_isShared_1018_ = v_isSharedCheck_1031_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v_a_1011_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1031_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_dyn_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1019_ = l_Std_Http_Extensions_empty;
v___x_1020_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
v_dyn_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1021_, 0, v___x_1020_);
lean_ctor_set(v_dyn_1021_, 1, v_a_1015_);
v___x_1022_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__21___closed__2));
v___x_1023_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1021_);
v___x_1024_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1022_, v___x_1023_, v_dyn_1021_, v___x_1019_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1024_);
v___x_1026_ = v___x_1017_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1028_, v___x_997_, v___x_1027_, v___f_999_);
return v___x_1029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__21___boxed(lean_object* v___x_1032_, lean_object* v___f_1033_, lean_object* v___f_1034_, lean_object* v_x_1035_, lean_object* v___y_1036_){
_start:
{
uint8_t v___x_13555__boxed_1037_; lean_object* v_res_1038_; 
v___x_13555__boxed_1037_ = lean_unbox(v___x_1032_);
v_res_1038_ = l_Std_Http_Server_serve___redArg___lam__21(v___x_13555__boxed_1037_, v___f_1033_, v___f_1034_, v_x_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20(uint8_t v_permitAcquired_1039_, lean_object* v___f_1040_, lean_object* v___x_1041_, lean_object* v___y_1042_, lean_object* v_connectionLimit_1043_, uint8_t v___x_1044_, lean_object* v___f_1045_, lean_object* v___x_1046_, lean_object* v_activeConnections_1047_, lean_object* v___f_1048_, lean_object* v___f_1049_, lean_object* v___f_1050_, lean_object* v_inst_1051_, lean_object* v_handler_1052_, lean_object* v_config_1053_, lean_object* v___f_1054_, lean_object* v___f_1055_, lean_object* v_x_1056_){
_start:
{
if (lean_obj_tag(v_x_1056_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v___f_1055_);
lean_dec_ref(v___f_1054_);
lean_dec_ref(v_config_1053_);
lean_dec(v_handler_1052_);
lean_dec_ref(v_inst_1051_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v___f_1049_);
lean_dec_ref(v___f_1048_);
lean_dec_ref(v_activeConnections_1047_);
lean_dec_ref(v___x_1046_);
lean_dec_ref(v___f_1045_);
lean_dec(v_connectionLimit_1043_);
lean_dec_ref(v___f_1040_);
v_a_1058_ = lean_ctor_get(v_x_1056_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_1056_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1060_ = v_x_1056_;
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v_x_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1125_; 
v_a_1067_ = lean_ctor_get(v_x_1056_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1056_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1069_ = v_x_1056_;
v_isShared_1070_ = v_isSharedCheck_1125_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v_x_1056_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1125_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
if (lean_obj_tag(v_a_1067_) == 0)
{
lean_dec_ref(v___f_1055_);
lean_dec_ref(v___f_1054_);
lean_dec_ref(v_config_1053_);
lean_dec(v_handler_1052_);
lean_dec_ref(v_inst_1051_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v___f_1049_);
lean_dec_ref(v___f_1048_);
lean_dec_ref(v_activeConnections_1047_);
lean_dec_ref(v___x_1046_);
if (v_permitAcquired_1039_ == 0)
{
lean_object* v___x_1071_; 
lean_del_object(v___x_1069_);
lean_dec_ref(v___f_1045_);
lean_dec(v_connectionLimit_1043_);
lean_inc_ref(v___y_1042_);
v___x_1071_ = lean_apply_3(v___f_1040_, v___x_1041_, v___y_1042_, lean_box(0));
return v___x_1071_;
}
else
{
if (lean_obj_tag(v_connectionLimit_1043_) == 1)
{
lean_object* v_val_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v___f_1040_);
v_val_1072_ = lean_ctor_get(v_connectionLimit_1043_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_connectionLimit_1043_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1074_ = v_connectionLimit_1043_;
v_isShared_1075_ = v_isSharedCheck_1085_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_val_1072_);
lean_dec(v_connectionLimit_1043_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1085_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = l_Std_Semaphore_release(v_val_1072_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1076_);
v___x_1078_ = v___x_1069_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1078_);
v___x_1080_ = v___x_1074_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1081_, v___x_1044_, v___x_1080_, v___f_1045_);
return v___x_1082_;
}
}
}
}
else
{
lean_object* v___x_1086_; 
lean_del_object(v___x_1069_);
lean_dec_ref(v___f_1045_);
lean_dec(v_connectionLimit_1043_);
lean_inc_ref(v___y_1042_);
v___x_1086_ = lean_apply_3(v___f_1040_, v___x_1041_, v___y_1042_, lean_box(0));
return v___x_1086_;
}
}
}
else
{
lean_object* v_val_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v___f_1045_);
lean_dec_ref(v___f_1040_);
v_val_1087_ = lean_ctor_get(v_a_1067_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_a_1067_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1089_ = v_a_1067_;
v_isShared_1090_ = v_isSharedCheck_1124_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_val_1087_);
lean_dec(v_a_1067_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1124_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___f_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; lean_object* v_val_1098_; lean_object* v___x_1107_; 
v___x_1091_ = lean_box(v_permitAcquired_1039_);
v___x_1092_ = lean_box(v___x_1044_);
lean_inc(v_val_1087_);
v___f_1093_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__18___boxed), 18, 15);
lean_closure_set(v___f_1093_, 0, v___x_1046_);
lean_closure_set(v___f_1093_, 1, v_activeConnections_1047_);
lean_closure_set(v___f_1093_, 2, v___f_1048_);
lean_closure_set(v___f_1093_, 3, v___f_1049_);
lean_closure_set(v___f_1093_, 4, v___f_1050_);
lean_closure_set(v___f_1093_, 5, v___x_1091_);
lean_closure_set(v___f_1093_, 6, v___x_1041_);
lean_closure_set(v___f_1093_, 7, v_connectionLimit_1043_);
lean_closure_set(v___f_1093_, 8, v___x_1092_);
lean_closure_set(v___f_1093_, 9, v_inst_1051_);
lean_closure_set(v___f_1093_, 10, v_val_1087_);
lean_closure_set(v___f_1093_, 11, v_handler_1052_);
lean_closure_set(v___f_1093_, 12, v_config_1053_);
lean_closure_set(v___f_1093_, 13, v___f_1054_);
lean_closure_set(v___f_1093_, 14, v___f_1055_);
lean_inc_ref(v___y_1042_);
v___f_1094_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__19___boxed), 4, 2);
lean_closure_set(v___f_1094_, 0, v___f_1093_);
lean_closure_set(v___f_1094_, 1, v___y_1042_);
v___x_1095_ = lean_box(v___x_1044_);
lean_inc_ref(v___f_1094_);
v___f_1096_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__21___boxed), 5, 3);
lean_closure_set(v___f_1096_, 0, v___x_1095_);
lean_closure_set(v___f_1096_, 1, v___f_1094_);
lean_closure_set(v___f_1096_, 2, v___f_1094_);
v___x_1107_ = lean_uv_tcp_getpeername(v_val_1087_);
lean_dec(v_val_1087_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 1);
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
v_val_1098_ = v___x_1113_;
goto v___jp_1097_;
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_a_1116_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1107_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1107_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 0);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
v_val_1098_ = v___x_1121_;
goto v___jp_1097_;
}
}
}
v___jp_1097_:
{
lean_object* v___x_1100_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v_val_1098_);
v___x_1100_ = v___x_1069_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_val_1098_);
v___x_1100_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1102_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1100_);
v___x_1102_ = v___x_1089_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1103_, v___x_1044_, v___x_1102_, v___f_1096_);
return v___x_1104_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__20___boxed(lean_object** _args){
lean_object* v_permitAcquired_1126_ = _args[0];
lean_object* v___f_1127_ = _args[1];
lean_object* v___x_1128_ = _args[2];
lean_object* v___y_1129_ = _args[3];
lean_object* v_connectionLimit_1130_ = _args[4];
lean_object* v___x_1131_ = _args[5];
lean_object* v___f_1132_ = _args[6];
lean_object* v___x_1133_ = _args[7];
lean_object* v_activeConnections_1134_ = _args[8];
lean_object* v___f_1135_ = _args[9];
lean_object* v___f_1136_ = _args[10];
lean_object* v___f_1137_ = _args[11];
lean_object* v_inst_1138_ = _args[12];
lean_object* v_handler_1139_ = _args[13];
lean_object* v_config_1140_ = _args[14];
lean_object* v___f_1141_ = _args[15];
lean_object* v___f_1142_ = _args[16];
lean_object* v_x_1143_ = _args[17];
lean_object* v___y_1144_ = _args[18];
_start:
{
uint8_t v_permitAcquired_boxed_1145_; uint8_t v___x_13637__boxed_1146_; lean_object* v_res_1147_; 
v_permitAcquired_boxed_1145_ = lean_unbox(v_permitAcquired_1126_);
v___x_13637__boxed_1146_ = lean_unbox(v___x_1131_);
v_res_1147_ = l_Std_Http_Server_serve___redArg___lam__20(v_permitAcquired_boxed_1145_, v___f_1127_, v___x_1128_, v___y_1129_, v_connectionLimit_1130_, v___x_13637__boxed_1146_, v___f_1132_, v___x_1133_, v_activeConnections_1134_, v___f_1135_, v___f_1136_, v___f_1137_, v_inst_1138_, v_handler_1139_, v_config_1140_, v___f_1141_, v___f_1142_, v_x_1143_);
lean_dec_ref(v___y_1129_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22(lean_object* v_a_1148_, lean_object* v___f_1149_, lean_object* v___f_1150_, uint8_t v___x_1151_, lean_object* v___f_1152_, lean_object* v_x_1153_){
_start:
{
if (lean_obj_tag(v_x_1153_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1163_; 
lean_dec_ref(v___f_1152_);
lean_dec_ref(v___f_1150_);
lean_dec_ref(v___f_1149_);
lean_dec(v_a_1148_);
v_a_1155_ = lean_ctor_get(v_x_1153_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_x_1153_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1157_ = v_x_1153_;
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v_x_1153_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_a_1164_ = lean_ctor_get(v_x_1153_, 0);
lean_inc(v_a_1164_);
lean_dec_ref(v_x_1153_);
v___x_1165_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_1148_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v___f_1149_);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_a_1164_);
lean_ctor_set(v___x_1167_, 1, v___f_1150_);
v___x_1168_ = lean_unsigned_to_nat(2u);
v___x_1169_ = lean_mk_empty_array_with_capacity(v___x_1168_);
v___x_1170_ = lean_array_push(v___x_1169_, v___x_1166_);
v___x_1171_ = lean_array_push(v___x_1170_, v___x_1167_);
v___x_1172_ = l_Std_Async_Selectable_one___redArg(v___x_1171_);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1173_, v___x_1151_, v___x_1172_, v___f_1152_);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__22___boxed(lean_object* v_a_1175_, lean_object* v___f_1176_, lean_object* v___f_1177_, lean_object* v___x_1178_, lean_object* v___f_1179_, lean_object* v_x_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v___x_13815__boxed_1182_; lean_object* v_res_1183_; 
v___x_13815__boxed_1182_ = lean_unbox(v___x_1178_);
v_res_1183_ = l_Std_Http_Server_serve___redArg___lam__22(v_a_1175_, v___f_1176_, v___f_1177_, v___x_13815__boxed_1182_, v___f_1179_, v_x_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23(uint8_t v___x_1184_, lean_object* v___f_1185_, lean_object* v___f_1186_, lean_object* v___x_1187_, lean_object* v_connectionLimit_1188_, lean_object* v___x_1189_, lean_object* v_activeConnections_1190_, lean_object* v___f_1191_, lean_object* v___f_1192_, lean_object* v___f_1193_, lean_object* v_inst_1194_, lean_object* v_handler_1195_, lean_object* v_config_1196_, lean_object* v___f_1197_, lean_object* v___f_1198_, lean_object* v_a_1199_, lean_object* v___f_1200_, lean_object* v___f_1201_, uint8_t v_permitAcquired_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___f_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___f_1212_; lean_object* v___x_1213_; lean_object* v___f_1214_; lean_object* v___x_1215_; 
lean_inc_ref_n(v___y_1203_, 3);
v___x_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___y_1203_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1207_, v___x_1184_, v___x_1206_, v___f_1185_);
lean_inc_ref(v___f_1186_);
v___f_1209_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_1209_, 0, v___f_1186_);
lean_closure_set(v___f_1209_, 1, v___y_1203_);
v___x_1210_ = lean_box(v_permitAcquired_1202_);
v___x_1211_ = lean_box(v___x_1184_);
v___f_1212_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__20___boxed), 19, 17);
lean_closure_set(v___f_1212_, 0, v___x_1210_);
lean_closure_set(v___f_1212_, 1, v___f_1186_);
lean_closure_set(v___f_1212_, 2, v___x_1187_);
lean_closure_set(v___f_1212_, 3, v___y_1203_);
lean_closure_set(v___f_1212_, 4, v_connectionLimit_1188_);
lean_closure_set(v___f_1212_, 5, v___x_1211_);
lean_closure_set(v___f_1212_, 6, v___f_1209_);
lean_closure_set(v___f_1212_, 7, v___x_1189_);
lean_closure_set(v___f_1212_, 8, v_activeConnections_1190_);
lean_closure_set(v___f_1212_, 9, v___f_1191_);
lean_closure_set(v___f_1212_, 10, v___f_1192_);
lean_closure_set(v___f_1212_, 11, v___f_1193_);
lean_closure_set(v___f_1212_, 12, v_inst_1194_);
lean_closure_set(v___f_1212_, 13, v_handler_1195_);
lean_closure_set(v___f_1212_, 14, v_config_1196_);
lean_closure_set(v___f_1212_, 15, v___f_1197_);
lean_closure_set(v___f_1212_, 16, v___f_1198_);
v___x_1213_ = lean_box(v___x_1184_);
v___f_1214_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__22___boxed), 7, 5);
lean_closure_set(v___f_1214_, 0, v_a_1199_);
lean_closure_set(v___f_1214_, 1, v___f_1200_);
lean_closure_set(v___f_1214_, 2, v___f_1201_);
lean_closure_set(v___f_1214_, 3, v___x_1213_);
lean_closure_set(v___f_1214_, 4, v___f_1212_);
v___x_1215_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1207_, v___x_1184_, v___x_1208_, v___f_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__23___boxed(lean_object** _args){
lean_object* v___x_1216_ = _args[0];
lean_object* v___f_1217_ = _args[1];
lean_object* v___f_1218_ = _args[2];
lean_object* v___x_1219_ = _args[3];
lean_object* v_connectionLimit_1220_ = _args[4];
lean_object* v___x_1221_ = _args[5];
lean_object* v_activeConnections_1222_ = _args[6];
lean_object* v___f_1223_ = _args[7];
lean_object* v___f_1224_ = _args[8];
lean_object* v___f_1225_ = _args[9];
lean_object* v_inst_1226_ = _args[10];
lean_object* v_handler_1227_ = _args[11];
lean_object* v_config_1228_ = _args[12];
lean_object* v___f_1229_ = _args[13];
lean_object* v___f_1230_ = _args[14];
lean_object* v_a_1231_ = _args[15];
lean_object* v___f_1232_ = _args[16];
lean_object* v___f_1233_ = _args[17];
lean_object* v_permitAcquired_1234_ = _args[18];
lean_object* v___y_1235_ = _args[19];
lean_object* v___y_1236_ = _args[20];
_start:
{
uint8_t v___x_13873__boxed_1237_; uint8_t v_permitAcquired_boxed_1238_; lean_object* v_res_1239_; 
v___x_13873__boxed_1237_ = lean_unbox(v___x_1216_);
v_permitAcquired_boxed_1238_ = lean_unbox(v_permitAcquired_1234_);
v_res_1239_ = l_Std_Http_Server_serve___redArg___lam__23(v___x_13873__boxed_1237_, v___f_1217_, v___f_1218_, v___x_1219_, v_connectionLimit_1220_, v___x_1221_, v_activeConnections_1222_, v___f_1223_, v___f_1224_, v___f_1225_, v_inst_1226_, v_handler_1227_, v_config_1228_, v___f_1229_, v___f_1230_, v_a_1231_, v___f_1232_, v___f_1233_, v_permitAcquired_boxed_1238_, v___y_1235_);
lean_dec_ref(v___y_1235_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24(lean_object* v___f_1240_, lean_object* v___y_1241_, lean_object* v_x_1242_){
_start:
{
if (lean_obj_tag(v_x_1242_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v___f_1240_);
v_a_1244_ = lean_ctor_get(v_x_1242_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_x_1242_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1246_ = v_x_1242_;
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v_x_1242_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1254_; 
v_a_1253_ = lean_ctor_get(v_x_1242_, 0);
lean_inc(v_a_1253_);
lean_dec_ref(v_x_1242_);
lean_inc_ref(v___y_1241_);
v___x_1254_ = lean_apply_3(v___f_1240_, v_a_1253_, v___y_1241_, lean_box(0));
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__24___boxed(lean_object* v___f_1255_, lean_object* v___y_1256_, lean_object* v_x_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Std_Http_Server_serve___redArg___lam__24(v___f_1255_, v___y_1256_, v_x_1257_);
lean_dec_ref(v___y_1256_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25(uint8_t v___x_1260_, uint8_t v___x_1261_, lean_object* v___f_1262_, lean_object* v_x_1263_){
_start:
{
if (lean_obj_tag(v_x_1263_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v___f_1262_);
v_a_1265_ = lean_ctor_get(v_x_1263_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_x_1263_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1267_ = v_x_1263_;
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v_x_1263_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
}
}
else
{
lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1284_; 
v_isSharedCheck_1284_ = !lean_is_exclusive(v_x_1263_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; 
v_unused_1285_ = lean_ctor_get(v_x_1263_, 0);
lean_dec(v_unused_1285_);
v___x_1275_ = v_x_1263_;
v_isShared_1276_ = v_isSharedCheck_1284_;
goto v_resetjp_1274_;
}
else
{
lean_dec(v_x_1263_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1284_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_box(v___x_1260_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1277_);
v___x_1279_ = v___x_1275_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1281_, v___x_1261_, v___x_1280_, v___f_1262_);
return v___x_1282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__25___boxed(lean_object* v___x_1286_, lean_object* v___x_1287_, lean_object* v___f_1288_, lean_object* v_x_1289_, lean_object* v___y_1290_){
_start:
{
uint8_t v___x_13977__boxed_1291_; uint8_t v___x_13978__boxed_1292_; lean_object* v_res_1293_; 
v___x_13977__boxed_1291_ = lean_unbox(v___x_1286_);
v___x_13978__boxed_1292_ = lean_unbox(v___x_1287_);
v_res_1293_ = l_Std_Http_Server_serve___redArg___lam__25(v___x_13977__boxed_1291_, v___x_13978__boxed_1292_, v___f_1288_, v_x_1289_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26(lean_object* v___f_1294_, uint8_t v___x_1295_, lean_object* v___f_1296_, lean_object* v_x_1297_){
_start:
{
if (lean_obj_tag(v_x_1297_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v___f_1296_);
lean_dec_ref(v___f_1294_);
v_a_1299_ = lean_ctor_get(v_x_1297_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_x_1297_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1301_ = v_x_1297_;
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v_x_1297_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
return v___x_1305_;
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_a_1308_ = lean_ctor_get(v_x_1297_, 0);
lean_inc(v_a_1308_);
lean_dec_ref(v_x_1297_);
v___x_1309_ = l_IO_Promise_result_x21___redArg(v_a_1308_);
lean_dec(v_a_1308_);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_task_map(v___f_1294_, v___x_1309_, v___x_1310_, v___x_1295_);
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
v___x_1313_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1310_, v___x_1295_, v___x_1312_, v___f_1296_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__26___boxed(lean_object* v___f_1314_, lean_object* v___x_1315_, lean_object* v___f_1316_, lean_object* v_x_1317_, lean_object* v___y_1318_){
_start:
{
uint8_t v___x_14036__boxed_1319_; lean_object* v_res_1320_; 
v___x_14036__boxed_1319_ = lean_unbox(v___x_1315_);
v_res_1320_ = l_Std_Http_Server_serve___redArg___lam__26(v___f_1314_, v___x_14036__boxed_1319_, v___f_1316_, v_x_1317_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28(uint8_t v___x_1321_, lean_object* v___f_1322_, lean_object* v_connectionLimit_1323_, lean_object* v___f_1324_, lean_object* v___f_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___y_1330_; 
if (lean_obj_tag(v_connectionLimit_1323_) == 1)
{
lean_object* v_val_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1351_; 
v_val_1333_ = lean_ctor_get(v_connectionLimit_1323_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_connectionLimit_1323_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1335_ = v_connectionLimit_1323_;
v_isShared_1336_ = v_isSharedCheck_1351_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_val_1333_);
lean_dec(v_connectionLimit_1323_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1351_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___f_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___f_1342_; lean_object* v___x_1343_; lean_object* v___f_1344_; lean_object* v___x_1346_; 
v___x_1337_ = l_Std_Semaphore_acquire(v_val_1333_);
lean_inc_ref(v___y_1327_);
v___f_1338_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__24___boxed), 4, 2);
lean_closure_set(v___f_1338_, 0, v___f_1324_);
lean_closure_set(v___f_1338_, 1, v___y_1327_);
v___x_1339_ = 1;
v___x_1340_ = lean_box(v___x_1339_);
v___x_1341_ = lean_box(v___x_1321_);
v___f_1342_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__25___boxed), 5, 3);
lean_closure_set(v___f_1342_, 0, v___x_1340_);
lean_closure_set(v___f_1342_, 1, v___x_1341_);
lean_closure_set(v___f_1342_, 2, v___f_1338_);
v___x_1343_ = lean_box(v___x_1321_);
v___f_1344_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__26___boxed), 5, 3);
lean_closure_set(v___f_1344_, 0, v___f_1325_);
lean_closure_set(v___f_1344_, 1, v___x_1343_);
lean_closure_set(v___f_1344_, 2, v___f_1342_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1337_);
v___x_1346_ = v___x_1335_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1337_);
v___x_1346_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
v___x_1348_ = lean_unsigned_to_nat(0u);
v___x_1349_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1348_, v___x_1321_, v___x_1347_, v___f_1344_);
v___y_1330_ = v___x_1349_;
goto v___jp_1329_;
}
}
}
else
{
lean_object* v___f_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec_ref(v___f_1325_);
lean_dec(v_connectionLimit_1323_);
lean_inc_ref(v___y_1327_);
v___f_1352_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__24___boxed), 4, 2);
lean_closure_set(v___f_1352_, 0, v___f_1324_);
lean_closure_set(v___f_1352_, 1, v___y_1327_);
v___x_1353_ = lean_box(v___x_1321_);
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1356_, v___x_1321_, v___x_1355_, v___f_1352_);
v___y_1330_ = v___x_1357_;
goto v___jp_1329_;
}
v___jp_1329_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1331_, v___x_1321_, v___y_1330_, v___f_1322_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__28___boxed(lean_object* v___x_1358_, lean_object* v___f_1359_, lean_object* v_connectionLimit_1360_, lean_object* v___f_1361_, lean_object* v___f_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
uint8_t v___x_14080__boxed_1366_; lean_object* v_res_1367_; 
v___x_14080__boxed_1366_ = lean_unbox(v___x_1358_);
v_res_1367_ = l_Std_Http_Server_serve___redArg___lam__28(v___x_14080__boxed_1366_, v___f_1359_, v_connectionLimit_1360_, v___f_1361_, v___f_1362_, v_b_1363_, v___y_1364_);
lean_dec_ref(v___y_1364_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27(lean_object* v___x_1368_, lean_object* v___f_1369_, lean_object* v___x_1370_, uint8_t v___x_1371_, lean_object* v___f_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_12499__overap_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_12499__overap_1375_ = l___private_Init_While_0__whileM_erased___redArg(v___x_1368_, v___f_1369_, v___x_1370_);
v___x_1376_ = lean_apply_2(v___x_12499__overap_1375_, v___y_1373_, lean_box(0));
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1377_, v___x_1371_, v___x_1376_, v___f_1372_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__27___boxed(lean_object* v___x_1379_, lean_object* v___f_1380_, lean_object* v___x_1381_, lean_object* v___x_1382_, lean_object* v___f_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v___x_14159__boxed_1386_; lean_object* v_res_1387_; 
v___x_14159__boxed_1386_ = lean_unbox(v___x_1382_);
v_res_1387_ = l_Std_Http_Server_serve___redArg___lam__27(v___x_1379_, v___f_1380_, v___x_1381_, v___x_14159__boxed_1386_, v___f_1383_, v___y_1384_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29(lean_object* v_a_1392_, lean_object* v___f_1393_, lean_object* v___x_1394_, lean_object* v___f_1395_, lean_object* v___f_1396_, lean_object* v___f_1397_, lean_object* v_inst_1398_, lean_object* v_handler_1399_, lean_object* v_config_1400_, lean_object* v___f_1401_, lean_object* v_a_1402_, lean_object* v___f_1403_, lean_object* v___f_1404_, lean_object* v___f_1405_, lean_object* v___f_1406_, lean_object* v___f_1407_, lean_object* v___f_1408_, lean_object* v_x_1409_){
_start:
{
if (lean_obj_tag(v_x_1409_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1419_; 
lean_dec_ref(v___f_1408_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___f_1406_);
lean_dec_ref(v___f_1405_);
lean_dec_ref(v___f_1404_);
lean_dec_ref(v___f_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v___f_1401_);
lean_dec_ref(v_config_1400_);
lean_dec(v_handler_1399_);
lean_dec_ref(v_inst_1398_);
lean_dec_ref(v___f_1397_);
lean_dec_ref(v___f_1396_);
lean_dec_ref(v___f_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___f_1393_);
lean_dec_ref(v_a_1392_);
v_a_1411_ = lean_ctor_get(v_x_1409_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_x_1409_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1413_ = v_x_1409_;
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v_x_1409_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
}
else
{
lean_object* v_context_1420_; lean_object* v_activeConnections_1421_; lean_object* v_connectionLimit_1422_; uint8_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___f_1425_; lean_object* v___f_1426_; lean_object* v___x_1427_; lean_object* v___f_1428_; lean_object* v___x_1429_; lean_object* v___f_1430_; lean_object* v___x_1431_; lean_object* v___f_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec_ref(v_x_1409_);
v_context_1420_ = lean_ctor_get(v_a_1392_, 0);
lean_inc_ref(v_context_1420_);
v_activeConnections_1421_ = lean_ctor_get(v_a_1392_, 1);
v_connectionLimit_1422_ = lean_ctor_get(v_a_1392_, 2);
v___x_1423_ = 0;
v___x_1424_ = lean_box(0);
v___f_1425_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__29___closed__0));
v___f_1426_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___lam__29___closed__1));
v___x_1427_ = lean_box(v___x_1423_);
lean_inc_ref(v_activeConnections_1421_);
lean_inc_ref(v___x_1394_);
lean_inc_n(v_connectionLimit_1422_, 2);
v___f_1428_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__23___boxed), 21, 18);
lean_closure_set(v___f_1428_, 0, v___x_1427_);
lean_closure_set(v___f_1428_, 1, v___f_1393_);
lean_closure_set(v___f_1428_, 2, v___f_1425_);
lean_closure_set(v___f_1428_, 3, v___x_1424_);
lean_closure_set(v___f_1428_, 4, v_connectionLimit_1422_);
lean_closure_set(v___f_1428_, 5, v___x_1394_);
lean_closure_set(v___f_1428_, 6, v_activeConnections_1421_);
lean_closure_set(v___f_1428_, 7, v___f_1395_);
lean_closure_set(v___f_1428_, 8, v___f_1396_);
lean_closure_set(v___f_1428_, 9, v___f_1397_);
lean_closure_set(v___f_1428_, 10, v_inst_1398_);
lean_closure_set(v___f_1428_, 11, v_handler_1399_);
lean_closure_set(v___f_1428_, 12, v_config_1400_);
lean_closure_set(v___f_1428_, 13, v___f_1401_);
lean_closure_set(v___f_1428_, 14, v___f_1426_);
lean_closure_set(v___f_1428_, 15, v_a_1402_);
lean_closure_set(v___f_1428_, 16, v___f_1403_);
lean_closure_set(v___f_1428_, 17, v___f_1404_);
v___x_1429_ = lean_box(v___x_1423_);
v___f_1430_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__28___boxed), 8, 5);
lean_closure_set(v___f_1430_, 0, v___x_1429_);
lean_closure_set(v___f_1430_, 1, v___f_1405_);
lean_closure_set(v___f_1430_, 2, v_connectionLimit_1422_);
lean_closure_set(v___f_1430_, 3, v___f_1428_);
lean_closure_set(v___f_1430_, 4, v___f_1406_);
v___x_1431_ = lean_box(v___x_1423_);
v___f_1432_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__27___boxed), 7, 5);
lean_closure_set(v___f_1432_, 0, v___x_1394_);
lean_closure_set(v___f_1432_, 1, v___f_1430_);
lean_closure_set(v___f_1432_, 2, v___x_1424_);
lean_closure_set(v___f_1432_, 3, v___x_1431_);
lean_closure_set(v___f_1432_, 4, v___f_1407_);
v___x_1433_ = lean_box(v___x_1423_);
v___x_1434_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed), 6, 5);
lean_closure_set(v___x_1434_, 0, lean_box(0));
lean_closure_set(v___x_1434_, 1, v_a_1392_);
lean_closure_set(v___x_1434_, 2, v___x_1433_);
lean_closure_set(v___x_1434_, 3, v___f_1432_);
lean_closure_set(v___x_1434_, 4, v_context_1420_);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_1436_, 0, lean_box(0));
lean_closure_set(v___x_1436_, 1, v___x_1434_);
v___x_1437_ = lean_io_as_task(v___x_1436_, v___x_1435_);
lean_dec_ref(v___x_1437_);
v___x_1438_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1));
v___x_1439_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1435_, v___x_1423_, v___x_1438_, v___f_1408_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__29___boxed(lean_object** _args){
lean_object* v_a_1440_ = _args[0];
lean_object* v___f_1441_ = _args[1];
lean_object* v___x_1442_ = _args[2];
lean_object* v___f_1443_ = _args[3];
lean_object* v___f_1444_ = _args[4];
lean_object* v___f_1445_ = _args[5];
lean_object* v_inst_1446_ = _args[6];
lean_object* v_handler_1447_ = _args[7];
lean_object* v_config_1448_ = _args[8];
lean_object* v___f_1449_ = _args[9];
lean_object* v_a_1450_ = _args[10];
lean_object* v___f_1451_ = _args[11];
lean_object* v___f_1452_ = _args[12];
lean_object* v___f_1453_ = _args[13];
lean_object* v___f_1454_ = _args[14];
lean_object* v___f_1455_ = _args[15];
lean_object* v___f_1456_ = _args[16];
lean_object* v_x_1457_ = _args[17];
lean_object* v___y_1458_ = _args[18];
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Std_Http_Server_serve___redArg___lam__29(v_a_1440_, v___f_1441_, v___x_1442_, v___f_1443_, v___f_1444_, v___f_1445_, v_inst_1446_, v_handler_1447_, v_config_1448_, v___f_1449_, v_a_1450_, v___f_1451_, v___f_1452_, v___f_1453_, v___f_1454_, v___f_1455_, v___f_1456_, v_x_1457_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30(lean_object* v___f_1460_, lean_object* v_a_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v_val_1465_; 
if (lean_obj_tag(v_x_1462_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v___f_1460_);
v_a_1470_ = lean_ctor_get(v_x_1462_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_x_1462_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1472_ = v_x_1462_;
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v_x_1462_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
}
else
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1491_; 
v_isSharedCheck_1491_ = !lean_is_exclusive(v_x_1462_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v_x_1462_, 0);
lean_dec(v_unused_1492_);
v___x_1480_ = v_x_1462_;
v_isShared_1481_ = v_isSharedCheck_1491_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v_x_1462_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1491_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_uv_tcp_nodelay(v_a_1461_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref(v___x_1482_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v_a_1483_);
v___x_1485_ = v___x_1480_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
v_val_1465_ = v___x_1485_;
goto v___jp_1464_;
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; 
v_a_1487_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1487_);
lean_dec_ref(v___x_1482_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set_tag(v___x_1480_, 0);
lean_ctor_set(v___x_1480_, 0, v_a_1487_);
v___x_1489_ = v___x_1480_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
v_val_1465_ = v___x_1489_;
goto v___jp_1464_;
}
}
}
}
v___jp_1464_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_val_1465_);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = 0;
v___x_1469_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1467_, v___x_1468_, v___x_1466_, v___f_1460_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__30___boxed(lean_object* v___f_1493_, lean_object* v_a_1494_, lean_object* v_x_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_1493_, v_a_1494_, v_x_1495_);
lean_dec(v_a_1494_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31(lean_object* v___f_1498_, lean_object* v_a_1499_, uint32_t v_backlog_1500_, lean_object* v_x_1501_){
_start:
{
lean_object* v_val_1504_; 
if (lean_obj_tag(v_x_1501_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v___f_1498_);
v_a_1509_ = lean_ctor_get(v_x_1501_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_x_1501_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1511_ = v_x_1501_;
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v_x_1501_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
}
}
else
{
lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1530_; 
v_isSharedCheck_1530_ = !lean_is_exclusive(v_x_1501_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_x_1501_, 0);
lean_dec(v_unused_1531_);
v___x_1519_ = v_x_1501_;
v_isShared_1520_ = v_isSharedCheck_1530_;
goto v_resetjp_1518_;
}
else
{
lean_dec(v_x_1501_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1530_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_uv_tcp_listen(v_a_1499_, v_backlog_1500_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref(v___x_1521_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v_a_1522_);
v___x_1524_ = v___x_1519_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
v_val_1504_ = v___x_1524_;
goto v___jp_1503_;
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; 
v_a_1526_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1526_);
lean_dec_ref(v___x_1521_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 0);
lean_ctor_set(v___x_1519_, 0, v_a_1526_);
v___x_1528_ = v___x_1519_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
v_val_1504_ = v___x_1528_;
goto v___jp_1503_;
}
}
}
}
v___jp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_val_1504_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = 0;
v___x_1508_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1506_, v___x_1507_, v___x_1505_, v___f_1498_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__31___boxed(lean_object* v___f_1532_, lean_object* v_a_1533_, lean_object* v_backlog_1534_, lean_object* v_x_1535_, lean_object* v___y_1536_){
_start:
{
uint32_t v_backlog_boxed_1537_; lean_object* v_res_1538_; 
v_backlog_boxed_1537_ = lean_unbox_uint32(v_backlog_1534_);
lean_dec(v_backlog_1534_);
v_res_1538_ = l_Std_Http_Server_serve___redArg___lam__31(v___f_1532_, v_a_1533_, v_backlog_boxed_1537_, v_x_1535_);
lean_dec(v_a_1533_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32(lean_object* v_a_1539_, lean_object* v___f_1540_, lean_object* v___x_1541_, lean_object* v___f_1542_, lean_object* v___f_1543_, lean_object* v___f_1544_, lean_object* v_inst_1545_, lean_object* v_handler_1546_, lean_object* v_config_1547_, lean_object* v___f_1548_, lean_object* v___f_1549_, lean_object* v___f_1550_, lean_object* v___f_1551_, lean_object* v___f_1552_, lean_object* v___f_1553_, lean_object* v___f_1554_, uint32_t v_backlog_1555_, lean_object* v_addr_1556_, lean_object* v_x_1557_){
_start:
{
if (lean_obj_tag(v_x_1557_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v___f_1554_);
lean_dec_ref(v___f_1553_);
lean_dec_ref(v___f_1552_);
lean_dec_ref(v___f_1551_);
lean_dec_ref(v___f_1550_);
lean_dec_ref(v___f_1549_);
lean_dec_ref(v___f_1548_);
lean_dec_ref(v_config_1547_);
lean_dec(v_handler_1546_);
lean_dec_ref(v_inst_1545_);
lean_dec_ref(v___f_1544_);
lean_dec_ref(v___f_1543_);
lean_dec_ref(v___f_1542_);
lean_dec_ref(v___x_1541_);
lean_dec_ref(v___f_1540_);
lean_dec_ref(v_a_1539_);
v_a_1559_ = lean_ctor_get(v_x_1557_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_x_1557_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1561_ = v_x_1557_;
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v_x_1557_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1591_; 
v_a_1568_ = lean_ctor_get(v_x_1557_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_x_1557_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1570_ = v_x_1557_;
v_isShared_1571_ = v_isSharedCheck_1591_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v_x_1557_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1591_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___f_1572_; lean_object* v___f_1573_; lean_object* v___x_1574_; lean_object* v___f_1575_; lean_object* v_val_1577_; lean_object* v___x_1582_; 
lean_inc_n(v_a_1568_, 3);
v___f_1572_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__29___boxed), 19, 17);
lean_closure_set(v___f_1572_, 0, v_a_1539_);
lean_closure_set(v___f_1572_, 1, v___f_1540_);
lean_closure_set(v___f_1572_, 2, v___x_1541_);
lean_closure_set(v___f_1572_, 3, v___f_1542_);
lean_closure_set(v___f_1572_, 4, v___f_1543_);
lean_closure_set(v___f_1572_, 5, v___f_1544_);
lean_closure_set(v___f_1572_, 6, v_inst_1545_);
lean_closure_set(v___f_1572_, 7, v_handler_1546_);
lean_closure_set(v___f_1572_, 8, v_config_1547_);
lean_closure_set(v___f_1572_, 9, v___f_1548_);
lean_closure_set(v___f_1572_, 10, v_a_1568_);
lean_closure_set(v___f_1572_, 11, v___f_1549_);
lean_closure_set(v___f_1572_, 12, v___f_1550_);
lean_closure_set(v___f_1572_, 13, v___f_1551_);
lean_closure_set(v___f_1572_, 14, v___f_1552_);
lean_closure_set(v___f_1572_, 15, v___f_1553_);
lean_closure_set(v___f_1572_, 16, v___f_1554_);
v___f_1573_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__30___boxed), 4, 2);
lean_closure_set(v___f_1573_, 0, v___f_1572_);
lean_closure_set(v___f_1573_, 1, v_a_1568_);
v___x_1574_ = lean_box_uint32(v_backlog_1555_);
v___f_1575_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__31___boxed), 5, 3);
lean_closure_set(v___f_1575_, 0, v___f_1573_);
lean_closure_set(v___f_1575_, 1, v_a_1568_);
lean_closure_set(v___f_1575_, 2, v___x_1574_);
v___x_1582_ = lean_uv_tcp_bind(v_a_1568_, v_addr_1556_);
lean_dec(v_a_1568_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_a_1583_);
v___x_1585_ = v___x_1570_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
v_val_1577_ = v___x_1585_;
goto v___jp_1576_;
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; 
v_a_1587_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1582_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set_tag(v___x_1570_, 0);
lean_ctor_set(v___x_1570_, 0, v_a_1587_);
v___x_1589_ = v___x_1570_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
v_val_1577_ = v___x_1589_;
goto v___jp_1576_;
}
}
v___jp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v_val_1577_);
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = 0;
v___x_1581_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1579_, v___x_1580_, v___x_1578_, v___f_1575_);
return v___x_1581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__32___boxed(lean_object** _args){
lean_object* v_a_1592_ = _args[0];
lean_object* v___f_1593_ = _args[1];
lean_object* v___x_1594_ = _args[2];
lean_object* v___f_1595_ = _args[3];
lean_object* v___f_1596_ = _args[4];
lean_object* v___f_1597_ = _args[5];
lean_object* v_inst_1598_ = _args[6];
lean_object* v_handler_1599_ = _args[7];
lean_object* v_config_1600_ = _args[8];
lean_object* v___f_1601_ = _args[9];
lean_object* v___f_1602_ = _args[10];
lean_object* v___f_1603_ = _args[11];
lean_object* v___f_1604_ = _args[12];
lean_object* v___f_1605_ = _args[13];
lean_object* v___f_1606_ = _args[14];
lean_object* v___f_1607_ = _args[15];
lean_object* v_backlog_1608_ = _args[16];
lean_object* v_addr_1609_ = _args[17];
lean_object* v_x_1610_ = _args[18];
lean_object* v___y_1611_ = _args[19];
_start:
{
uint32_t v_backlog_boxed_1612_; lean_object* v_res_1613_; 
v_backlog_boxed_1612_ = lean_unbox_uint32(v_backlog_1608_);
lean_dec(v_backlog_1608_);
v_res_1613_ = l_Std_Http_Server_serve___redArg___lam__32(v_a_1592_, v___f_1593_, v___x_1594_, v___f_1595_, v___f_1596_, v___f_1597_, v_inst_1598_, v_handler_1599_, v_config_1600_, v___f_1601_, v___f_1602_, v___f_1603_, v___f_1604_, v___f_1605_, v___f_1606_, v___f_1607_, v_backlog_boxed_1612_, v_addr_1609_, v_x_1610_);
lean_dec_ref(v_addr_1609_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33(lean_object* v___f_1614_, lean_object* v___x_1615_, lean_object* v___f_1616_, lean_object* v___f_1617_, lean_object* v_inst_1618_, lean_object* v_handler_1619_, lean_object* v_config_1620_, lean_object* v___f_1621_, lean_object* v___f_1622_, lean_object* v___f_1623_, lean_object* v___f_1624_, lean_object* v___f_1625_, lean_object* v___f_1626_, uint32_t v_backlog_1627_, lean_object* v_addr_1628_, lean_object* v_x_1629_){
_start:
{
if (lean_obj_tag(v_x_1629_) == 0)
{
lean_object* v___x_1631_; 
lean_dec_ref(v_addr_1628_);
lean_dec_ref(v___f_1626_);
lean_dec_ref(v___f_1625_);
lean_dec_ref(v___f_1624_);
lean_dec_ref(v___f_1623_);
lean_dec_ref(v___f_1622_);
lean_dec_ref(v___f_1621_);
lean_dec_ref(v_config_1620_);
lean_dec(v_handler_1619_);
lean_dec_ref(v_inst_1618_);
lean_dec_ref(v___f_1617_);
lean_dec_ref(v___f_1616_);
lean_dec_ref(v___x_1615_);
lean_dec_ref(v___f_1614_);
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v_x_1629_);
return v___x_1631_;
}
else
{
lean_object* v_a_1632_; lean_object* v___f_1633_; lean_object* v___f_1634_; lean_object* v___f_1635_; lean_object* v___x_1636_; lean_object* v___f_1637_; lean_object* v_val_1639_; lean_object* v___x_1644_; 
v_a_1632_ = lean_ctor_get(v_x_1629_, 0);
lean_inc_n(v_a_1632_, 2);
v___f_1633_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1633_, 0, v_x_1629_);
v___f_1634_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1634_, 0, v_a_1632_);
v___f_1635_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed), 5, 1);
lean_closure_set(v___f_1635_, 0, v___f_1634_);
v___x_1636_ = lean_box_uint32(v_backlog_1627_);
v___f_1637_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__32___boxed), 20, 18);
lean_closure_set(v___f_1637_, 0, v_a_1632_);
lean_closure_set(v___f_1637_, 1, v___f_1614_);
lean_closure_set(v___f_1637_, 2, v___x_1615_);
lean_closure_set(v___f_1637_, 3, v___f_1616_);
lean_closure_set(v___f_1637_, 4, v___f_1617_);
lean_closure_set(v___f_1637_, 5, v___f_1635_);
lean_closure_set(v___f_1637_, 6, v_inst_1618_);
lean_closure_set(v___f_1637_, 7, v_handler_1619_);
lean_closure_set(v___f_1637_, 8, v_config_1620_);
lean_closure_set(v___f_1637_, 9, v___f_1621_);
lean_closure_set(v___f_1637_, 10, v___f_1622_);
lean_closure_set(v___f_1637_, 11, v___f_1623_);
lean_closure_set(v___f_1637_, 12, v___f_1624_);
lean_closure_set(v___f_1637_, 13, v___f_1625_);
lean_closure_set(v___f_1637_, 14, v___f_1626_);
lean_closure_set(v___f_1637_, 15, v___f_1633_);
lean_closure_set(v___f_1637_, 16, v___x_1636_);
lean_closure_set(v___f_1637_, 17, v_addr_1628_);
v___x_1644_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 1);
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
v_val_1639_ = v___x_1650_;
goto v___jp_1638_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v_a_1653_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1644_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1644_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set_tag(v___x_1655_, 0);
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
v_val_1639_ = v___x_1658_;
goto v___jp_1638_;
}
}
}
v___jp_1638_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; 
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_val_1639_);
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = 0;
v___x_1643_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1641_, v___x_1642_, v___x_1640_, v___f_1637_);
return v___x_1643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___lam__33___boxed(lean_object** _args){
lean_object* v___f_1661_ = _args[0];
lean_object* v___x_1662_ = _args[1];
lean_object* v___f_1663_ = _args[2];
lean_object* v___f_1664_ = _args[3];
lean_object* v_inst_1665_ = _args[4];
lean_object* v_handler_1666_ = _args[5];
lean_object* v_config_1667_ = _args[6];
lean_object* v___f_1668_ = _args[7];
lean_object* v___f_1669_ = _args[8];
lean_object* v___f_1670_ = _args[9];
lean_object* v___f_1671_ = _args[10];
lean_object* v___f_1672_ = _args[11];
lean_object* v___f_1673_ = _args[12];
lean_object* v_backlog_1674_ = _args[13];
lean_object* v_addr_1675_ = _args[14];
lean_object* v_x_1676_ = _args[15];
lean_object* v___y_1677_ = _args[16];
_start:
{
uint32_t v_backlog_boxed_1678_; lean_object* v_res_1679_; 
v_backlog_boxed_1678_ = lean_unbox_uint32(v_backlog_1674_);
lean_dec(v_backlog_1674_);
v_res_1679_ = l_Std_Http_Server_serve___redArg___lam__33(v___f_1661_, v___x_1662_, v___f_1663_, v___f_1664_, v_inst_1665_, v_handler_1666_, v_config_1667_, v___f_1668_, v___f_1669_, v___f_1670_, v___f_1671_, v___f_1672_, v___f_1673_, v_backlog_boxed_1678_, v_addr_1675_, v_x_1676_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg(lean_object* v_inst_1686_, lean_object* v_addr_1687_, lean_object* v_handler_1688_, lean_object* v_config_1689_, uint32_t v_backlog_1690_){
_start:
{
lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___f_1694_; lean_object* v___f_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___f_1698_; lean_object* v___f_1699_; lean_object* v___f_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___f_1703_; lean_object* v_val_1705_; lean_object* v___x_1710_; lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v___f_1692_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__0));
v___f_1693_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__1));
v___f_1694_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0));
v___f_1695_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__2));
v___f_1696_ = ((lean_object*)(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5));
v___f_1697_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__3));
v___f_1698_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__4));
v___f_1699_ = ((lean_object*)(l_Std_Http_Server_serve___redArg___closed__5));
v___f_1700_ = ((lean_object*)(l_Std_Http_Server_waitShutdown___closed__0));
v___x_1701_ = l_Std_Async_ContextAsync_instMonad;
v___x_1702_ = lean_box_uint32(v_backlog_1690_);
lean_inc_ref(v_config_1689_);
v___f_1703_ = lean_alloc_closure((void*)(l_Std_Http_Server_serve___redArg___lam__33___boxed), 17, 15);
lean_closure_set(v___f_1703_, 0, v___f_1699_);
lean_closure_set(v___f_1703_, 1, v___x_1701_);
lean_closure_set(v___f_1703_, 2, v___f_1694_);
lean_closure_set(v___f_1703_, 3, v___f_1696_);
lean_closure_set(v___f_1703_, 4, v_inst_1686_);
lean_closure_set(v___f_1703_, 5, v_handler_1688_);
lean_closure_set(v___f_1703_, 6, v_config_1689_);
lean_closure_set(v___f_1703_, 7, v___f_1695_);
lean_closure_set(v___f_1703_, 8, v___f_1698_);
lean_closure_set(v___f_1703_, 9, v___f_1697_);
lean_closure_set(v___f_1703_, 10, v___f_1693_);
lean_closure_set(v___f_1703_, 11, v___f_1700_);
lean_closure_set(v___f_1703_, 12, v___f_1692_);
lean_closure_set(v___f_1703_, 13, v___x_1702_);
lean_closure_set(v___f_1703_, 14, v_addr_1687_);
v___x_1710_ = l_Std_Http_Server_new(v_config_1689_);
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v___jp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_val_1705_);
v___x_1707_ = lean_unsigned_to_nat(0u);
v___x_1708_ = 0;
v___x_1709_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1707_, v___x_1708_, v___x_1706_, v___f_1703_);
return v___x_1709_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 1);
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
v_val_1705_ = v___x_1716_;
goto v___jp_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___redArg___boxed(lean_object* v_inst_1719_, lean_object* v_addr_1720_, lean_object* v_handler_1721_, lean_object* v_config_1722_, lean_object* v_backlog_1723_, lean_object* v_a_1724_){
_start:
{
uint32_t v_backlog_boxed_1725_; lean_object* v_res_1726_; 
v_backlog_boxed_1725_ = lean_unbox_uint32(v_backlog_1723_);
lean_dec(v_backlog_1723_);
v_res_1726_ = l_Std_Http_Server_serve___redArg(v_inst_1719_, v_addr_1720_, v_handler_1721_, v_config_1722_, v_backlog_boxed_1725_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve(lean_object* v_00_u03c3_1727_, lean_object* v_inst_1728_, lean_object* v_addr_1729_, lean_object* v_handler_1730_, lean_object* v_config_1731_, uint32_t v_backlog_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Std_Http_Server_serve___redArg(v_inst_1728_, v_addr_1729_, v_handler_1730_, v_config_1731_, v_backlog_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serve___boxed(lean_object* v_00_u03c3_1735_, lean_object* v_inst_1736_, lean_object* v_addr_1737_, lean_object* v_handler_1738_, lean_object* v_config_1739_, lean_object* v_backlog_1740_, lean_object* v_a_1741_){
_start:
{
uint32_t v_backlog_boxed_1742_; lean_object* v_res_1743_; 
v_backlog_boxed_1742_ = lean_unbox_uint32(v_backlog_1740_);
lean_dec(v_backlog_1740_);
v_res_1743_ = l_Std_Http_Server_serve(v_00_u03c3_1735_, v_inst_1736_, v_addr_1737_, v_handler_1738_, v_config_1739_, v_backlog_boxed_1742_);
return v_res_1743_;
}
}
lean_object* runtime_initialize_Std_Async(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_TCP(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_CancellationToken(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Semaphore(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Handler(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Connection(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Server(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_CancellationToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Semaphore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server_Handler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server_Connection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Server(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Async(uint8_t builtin);
lean_object* initialize_Std_Async_TCP(uint8_t builtin);
lean_object* initialize_Std_Sync_CancellationToken(uint8_t builtin);
lean_object* initialize_Std_Sync_Semaphore(uint8_t builtin);
lean_object* initialize_Std_Http_Server_Config(uint8_t builtin);
lean_object* initialize_Std_Http_Server_Handler(uint8_t builtin);
lean_object* initialize_Std_Http_Server_Connection(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Server(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_CancellationToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Semaphore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Server_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Server_Handler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Server_Connection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Server(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Server(builtin);
}
#ifdef __cplusplus
}
#endif
